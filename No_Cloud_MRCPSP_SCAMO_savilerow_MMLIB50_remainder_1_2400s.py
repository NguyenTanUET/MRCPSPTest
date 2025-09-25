"""
MRCPSP Block-Based Staircase Encoding với Precedence-Aware Adaptive Width
Batch runner: quét toàn bộ .mm trong data/MMLIB50, giải với timeout 2400s/instance,
ghi CSV định kỳ 10 dòng/lần vào result/MMLIB50/.
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
import time
import math
from pathlib import Path
import csv
from datetime import datetime
import multiprocessing as mp
import tempfile, shutil
from concurrent.futures import ThreadPoolExecutor, as_completed
import subprocess, sys, json, os, signal, re, uuid, traceback, stat
from pathlib import Path

# GCS (tùy chọn)
try:
    from google.cloud import storage  # pip install google-cloud-storage
    _GCS_AVAILABLE = True
except Exception:
    storage = None
    _GCS_AVAILABLE = False

# Các cột cố định trong CSV
FIELDS = ["instance", "horizon", "variables", "clauses",
          "makespan", "status", "Solve time", "timeout"]


def clean_row(row: dict) -> dict:
    return {k: row.get(k, "") for k in FIELDS}

# ==========================
#  Phần ENCODER (giữ nguyên + bổ sung vài trường thống kê)
# ==========================

class MRCPSPBlockBasedStaircase:
    """MRCPSP Encoder với precedence-aware adaptive block width"""

    def __init__(self, mm_reader):
        self.cnf = CNF()
        self.vpool = IDPool()

        # Data từ reader
        self.jobs = mm_reader.data['num_jobs']
        self.horizon = mm_reader.get_horizon()
        self.renewable_resources = mm_reader.data['num_renewable']
        self.nonrenewable_resources = mm_reader.data['num_nonrenewable']

        self.R_capacity = mm_reader.data['renewable_capacity']
        self.N_capacity = mm_reader.data['nonrenewable_capacity']

        self.precedence = mm_reader.data['precedence']
        self.job_modes = mm_reader.data['job_modes']

        # Time windows
        self._preprocess_all()
        # Precedence-aware block widths
        self.precedence_widths = {}  # {(pred, succ): width}
        self.calculate_precedence_widths()

        # Block structures - now organized by precedence pairs
        self.precedence_blocks = {}  # {(pred, succ): blocks}
        self.job_blocks = {}  # {job: all_blocks} - aggregated view
        self.register_bits = {}
        self.block_connections = []

        # De-dup helpers
        self.connected_pairs = set()
        self.encoded_blocks = set()

        # Statistics
        self.stats = {
            'variables': 0,
            'clauses': 0,
            'register_bits': 0,
            'connection_clauses': 0,
        }
        self.last_var_count = 0
        self.last_clause_count = 0

    def _remove_infeasible_and_dominated_modes(self):
        """1) Bỏ mode không khả thi (vượt capacity)  2) Bỏ mode bị chi phối (dominated)."""
        R = self.renewable_resources
        new_modes = {}
        for j, modes in self.job_modes.items():
            # 1) lọc mode không khả thi
            feas = []
            for (dur, req) in modes:
                ok = True
                # renewables
                for r in range(R):
                    if r < len(req) and req[r] > self.R_capacity[r]:
                        ok = False
                        break
                # non-renewables
                if ok:
                    for k in range(self.nonrenewable_resources):
                        idx = R + k
                        if idx < len(req) and req[idx] > self.N_capacity[k]:
                            ok = False
                            break
                if ok:
                    feas.append((int(dur), list(map(int, req))))
            # 2) loại dominated
            keep = []
            for a, (da, ra) in enumerate(feas):
                dominated = False
                for b, (db, rb) in enumerate(feas):
                    if a == b: continue
                    leq_all = (db <= da) and all(rb[i] <= ra[i] for i in range(len(ra)))
                    strict = (db < da) or any(rb[i] < ra[i] for i in range(len(ra)))
                    if leq_all and strict:
                        dominated = True
                        break
                if not dominated:
                    keep.append((da, ra))
            # không để rỗng
            new_modes[j] = keep if keep else feas
        self.job_modes = new_modes

    def _eo_reduce_nonrenewables_inplace(self):
        """EO-reduction như trong tài liệu: trừ m_i vào dữ liệu + giảm B_k."""
        R = self.renewable_resources
        for k in range(self.nonrenewable_resources):
            idx = R + k
            mins = {}
            for j, modes in self.job_modes.items():
                vals = [(m[1][idx] if idx < len(m[1]) else 0) for m in modes]
                mins[j] = min(vals) if vals else 0
            red = sum(mins.values())
            # giảm capacity
            self.N_capacity[k] = max(0, self.N_capacity[k] - red)
            # trừ m_i trên từng mode
            for j, modes in self.job_modes.items():
                mi = mins[j]
                for t in range(len(modes)):
                    dur, req = modes[t]
                    if idx < len(req):
                        req[idx] = max(0, req[idx] - mi)
                    modes[t] = (dur, req)

    def _transitive_reduction(self):
        """Bỏ cung bắc cầu trong precedence."""
        n = self.jobs
        succ = {u: set(self.precedence.get(u, [])) for u in range(1, n + 1)}
        # Floyd–Warshall kiểu reachability
        reach = {u: set(succ[u]) for u in range(1, n + 1)}
        changed = True
        while changed:
            changed = False
            for u in range(1, n + 1):
                add = set()
                for v in list(reach[u]):
                    add |= reach[v]
                if not add.issubset(reach[u]):
                    reach[u] |= add
                    changed = True
        # bỏ cạnh (u,w) nếu tồn tại v: u->v và v->w
        for u in range(1, n + 1):
            to_remove = set()
            for w in succ[u]:
                for v in succ[u]:
                    if v != w and w in reach[v]:
                        to_remove.add(w)
                        break
            if to_remove:
                succ[u] -= to_remove
        self.precedence = {u: sorted(list(succ[u])) for u in succ if succ[u]}

    def _compute_time_windows_cpm(self):
        """ES forward & LF backward theo min duration; LS = LF - min duration."""
        # topo bằng BFS
        preds = {j: set() for j in range(1, self.jobs + 1)}
        for u, Vs in self.precedence.items():
            for v in Vs:
                preds[v].add(u)
        from collections import deque
        q = deque([j for j in range(1, self.jobs + 1) if not preds[j]])
        order = []
        succ = {u: set(self.precedence.get(u, [])) for u in range(1, self.jobs + 1)}
        indeg = {j: len(preds[j]) for j in preds}
        while q:
            u = q.popleft()
            order.append(u)
            for v in succ[u]:
                indeg[v] -= 1
                if indeg[v] == 0: q.append(v)

        min_dur = {j: (min(m[0] for m in self.job_modes[j]) if self.job_modes.get(j) else 0)
                   for j in range(1, self.jobs + 1)}
        # ES
        self.ES = {j: 0 for j in range(1, self.jobs + 1)}
        for u in order:
            for v in succ[u]:
                self.ES[v] = max(self.ES[v], self.ES[u] + min_dur[u])
        # LF/LS
        sink = self.jobs
        H = self.horizon
        LF = {j: H for j in range(1, self.jobs + 1)}
        rev = {j: set() for j in range(1, self.jobs + 1)}
        for u in succ:
            for v in succ[u]:
                rev[v].add(u)
        for u in reversed(order):
            if not succ[u]:  # nếu là sink hoặc không có kế tiếp
                LF[u] = min(LF[u], H)
            else:
                LF[u] = min(LF[u], min(LF[v] - min_dur[v] for v in succ[u]))
        self.LS = {j: max(0, LF[j] - min_dur[j]) for j in LF}

    def _extend_precedence_by_time_windows(self):
        """
        Extended precedence set (EPS) từ ES/LS với d_min.
        Luật:
          - nếu LS[j] < ES[i] + dmin[i]  ⇒  i -> j
          - nếu LS[i] < ES[j] + dmin[j]  ⇒  j -> i
        Chỉ thêm cạnh thuận theo thứ tự topo để tránh tạo vòng.
        Trả về: số cạnh mới đã thêm.
        """
        n = self.jobs
        # succ là đồ thị hiện tại
        succ = {u: set(self.precedence.get(u, [])) for u in range(1, n + 1)}

        # topo hiện tại (từ _compute_time_windows_cpm đã có)
        preds = {j: set() for j in range(1, n + 1)}
        for u, Vs in succ.items():
            for v in Vs:
                preds[v].add(u)
        from collections import deque
        q = deque([j for j in range(1, n + 1) if not preds[j]])
        topo = []
        indeg = {j: len(preds[j]) for j in preds}
        while q:
            u = q.popleft()
            topo.append(u)
            for v in succ[u]:
                indeg[v] -= 1
                if indeg[v] == 0:
                    q.append(v)
        pos = {node: i for i, node in enumerate(topo)}

        # d_min
        dmin = {j: (min(m[0] for m in self.job_modes[j]) if self.job_modes.get(j) else 0)
                for j in range(1, n + 1)}

        added = 0
        # duyệt tất cả cặp i != j chưa có liên hệ trực tiếp
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                if j in succ[i] or i in succ[j]:
                    continue  # đã có cạnh (i->j) hoặc (j->i)

                # Luật TW ⇒ hướng ưu tiên theo thứ tự topo để tránh vòng
                must_i_before_j = (self.LS[j] < self.ES[i] + dmin[i])
                must_j_before_i = (self.LS[i] < self.ES[j] + dmin[j])

                if must_i_before_j and (pos.get(i, -1) < pos.get(j, 10 ** 9)):
                    succ[i].add(j)
                    added += 1
                elif must_j_before_i and (pos.get(j, -1) < pos.get(i, 10 ** 9)):
                    succ[j].add(i)
                    added += 1

        if added > 0:
            # cập nhật và transitive reduction
            self.precedence = {u: sorted(list(succ[u])) for u in succ if succ[u]}
            # giảm bắc cầu
            self._transitive_reduction()
        return added

    def _preprocess_all(self):
        # 1) lọc mode + EO reduction
        self._remove_infeasible_and_dominated_modes()
        self._eo_reduce_nonrenewables_inplace()

        # 2) Lặp: reduce -> CPM -> EPS -> (có thêm cạnh?) -> lặp
        rounds = 0
        while True:
            rounds += 1
            self._transitive_reduction()
            self._compute_time_windows_cpm()
            added = self._extend_precedence_by_time_windows()
            # nếu không thêm nữa hoặc đã lặp 3 vòng thì dừng
            if added == 0 or rounds >= 3:
                break

        # 3) Sau cùng tính lại time windows
        self._compute_time_windows_cpm()

    def get_adaptive_width_for_precedence(self, pred_job, succ_job):
        """
        Tính block width cho successor dựa trên relationship với predecessor
        """

        # 1. Analyze time window interaction
        pred_durations = [mode[0] for mode in self.job_modes[pred_job]]
        pred_min_duration = min(pred_durations)
        pred_max_duration = max(pred_durations)

        # Time range where successor can start given predecessor
        earliest_succ = self.ES[pred_job] + pred_min_duration
        latest_succ = self.LS[pred_job] + pred_max_duration

        # Actual constrained window for successor
        constrained_start = max(self.ES[succ_job], earliest_succ)
        constrained_end = min(self.LS[succ_job], latest_succ)

        # Effective window size
        effective_window = max(0, constrained_end - constrained_start + 1)

        # 2. Duration variability of predecessor (affects uncertainty)
        duration_variability = pred_max_duration - pred_min_duration

        # 3. Mode complexity
        pred_modes = len(self.job_modes[pred_job])
        succ_modes = len(self.job_modes[succ_job])
        mode_combinations = pred_modes * succ_modes

        # 4. Calculate adaptive width
        if effective_window <= 0:
            # No real constraint - use default
            base_width = 10
        elif effective_window <= 5:
            # Very tight constraint - minimum width
            base_width = 3
        elif effective_window <= 15:
            # Tight constraint - small blocks
            base_width = 4
        elif effective_window <= 30:
            # Moderate constraint
            base_width = int(math.sqrt(effective_window))
        else:
            # Loose constraint - larger blocks ok
            base_width = min(12, int(effective_window / 6))

        # Adjust for duration variability
        if duration_variability >= 5:
            # High variability - need smaller blocks for precision
            base_width = max(3, base_width - 2)
        elif duration_variability == 0:
            # Fixed duration - can use larger blocks
            base_width = min(15, base_width + 2)

        # Adjust for mode complexity
        if mode_combinations > 9:
            # Many combinations - need flexibility
            base_width = max(3, base_width - 1)

        # Final bounds
        return max(3, min(base_width, 15))

    def calculate_precedence_widths(self):
        """Calculate block widths for all precedence relationships"""
        print("\n=== PRECEDENCE-AWARE BLOCK WIDTHS ===")
        print(f"{'Pred→Succ':<12} {'Effective Window':<18} {'Duration Var':<15} {'Modes':<10} {'Width':<8}")
        print("-" * 70)

        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence:
                continue

            for succ in self.precedence[pred]:
                width = self.get_adaptive_width_for_precedence(pred, succ)
                self.precedence_widths[(pred, succ)] = width

                # Calculate details for display
                pred_durations = [mode[0] for mode in self.job_modes[pred]]
                duration_var = max(pred_durations) - min(pred_durations)

                earliest = self.ES[pred] + min(pred_durations)
                latest = self.LS[pred] + max(pred_durations)
                effective_start = max(self.ES[succ], earliest)
                effective_end = min(self.LS[succ], latest)
                effective_window = max(0, effective_end - effective_start + 1)

                modes = f"{len(self.job_modes[pred])}×{len(self.job_modes[succ])}"

                print(f"{pred:3d}→{succ:3d}     [{effective_start:3d},{effective_end:3d}] ({effective_window:3d})     "
                      f"{duration_var:<15} {modes:<10} {width:<8}")

        # Statistics
        if self.precedence_widths:
            widths = list(self.precedence_widths.values())
            print(f"\nWidth statistics:")
            print(f"  Average: {sum(widths) / len(widths):.1f}")
            print(f"  Min: {min(widths)}, Max: {max(widths)}")
            print(f"  Total precedence pairs: {len(self.precedence_widths)}")

    def get_or_build_precedence_blocks(self, pred, succ):
        """
        Lấy (hoặc tạo-lần-đầu) danh sách block cho cung (pred->succ).
        Đảm bảo: block đã được encode AMO và connect tuần tự đúng 1 lần.
        """
        key = (pred, succ)
        blocks = self.precedence_blocks.get(key)
        if blocks is None:
            # Tạo block theo cung (cửa sổ hẹp, width thích nghi)
            blocks = self.create_blocks_for_precedence(pred, succ)
            blocks = sorted(blocks, key=lambda b: b[1])  # sort theo start time

            # Encode AMO cho từng block (idempotent nhờ self.encoded_blocks)
            for (bid, st, en, _bt, _a, _b) in blocks:
                self.encode_amo_block(bid, succ, st, en)

            # Connect các block trong CÙNG cung (idempotent nhờ self.connected_pairs)
            for i in range(len(blocks) - 1):
                self.connect_blocks(blocks[i][0], blocks[i + 1][0])

            self.precedence_blocks[key] = blocks

        return blocks

    def create_blocks_for_precedence(self, pred_job, succ_job):
        """
        Create blocks for successor based on precedence relationship
        Each precedence pair gets its own block structure
        """
        width = self.precedence_widths.get((pred_job, succ_job), 10)

        # Determine the relevant window for this precedence
        pred_durations = [mode[0] for mode in self.job_modes[pred_job]]
        earliest_succ = self.ES[pred_job] + min(pred_durations)
        latest_succ = self.LS[pred_job] + max(pred_durations)

        window_start = max(self.ES[succ_job], earliest_succ)
        window_end = min(self.LS[succ_job] + 1, latest_succ + 1)

        blocks = []
        block_id_base = f"J{succ_job}_W{window_start}_{window_end}_W{width}"  # successor-based id for sharing

        if window_end > window_start:
            num_blocks = (window_end - window_start + width - 1) // width

            for i in range(num_blocks):
                start = window_start + i * width
                end = min(start + width, window_end)

                if start < end:
                    block_id = f"{block_id_base}_{i}"

                    # First and last blocks are AMO, middle blocks have both AMO and AMZ
                    if start < end:
                        block_id = f"{block_id_base}_{i}"
                        blocks.append((block_id, start, end, 'AMO', pred_job, succ_job))

        # Store blocks for this precedence
        self.precedence_blocks[(pred_job, succ_job)] = blocks

        return blocks

    def create_blocks_for_job(self, job, width=None):
        es, ls = self.ES[job], self.LS[job]
        if width is None:
            win = max(1, ls - es + 1)
            width = max(6, int(math.sqrt(win)))  # simple adaptive width
        blocks = []
        window_start, window_end = es, ls + 1
        if window_end > window_start:
            num_blocks = (window_end - window_start + width - 1) // width
            for i in range(num_blocks):
                start = window_start + i * width
                end = min(start + width, window_end)
                if start < end:
                    block_id = f"J{job}_B{i}_{start}_{end}"
                    blocks.append((block_id, start, end, 'AMO', job, job))
        # store
        self.job_blocks[job] = blocks
        return blocks

    def create_variables(self, time_limit=None):
        """Create all variables"""
        Tmax = (time_limit if time_limit is not None else self.horizon + 1)

        # s_{j,t} variables for start times
        self.s_vars = {}
        for j in range(1, self.jobs + 1):
            self.s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = self.vpool.id(f's_{j}_{t}')
                self.s_vars[j][t] = var
                self.stats['variables'] += 1

        # sm_{j,m} variables for modes
        self.sm_vars = {}
        for j in range(1, self.jobs + 1):
            self.sm_vars[j] = {}
            for m in range(len(self.job_modes[j])):
                var = self.vpool.id(f'sm_{j}_{m}')
                self.sm_vars[j][m] = var
                self.stats['variables'] += 1

        # u_{j,t,m} process variables  (BỎ MODE KHÔNG DÙNG RENEWABLE)
        self.u_vars = {}
        for j in range(1, self.jobs + 1):
            self.u_vars[j] = {}
            for t in range(Tmax):
                self.u_vars[j][t] = {}
                for m in range(len(self.job_modes[j])):
                    dur, req = self.job_modes[j][m]
                    # BỎ nếu mode không dùng tài nguyên tái tạo
                    uses_any_R = any((k < self.renewable_resources and (len(req) > k and req[k] > 0))
                                     for k in range(self.renewable_resources))
                    if not uses_any_R and self.renewable_resources > 0:
                        continue

                    if t - dur + 1 <= self.LS[j] and t >= self.ES[j]:
                        var = self.vpool.id(f'u_{j}_{t}_{m}')
                        self.u_vars[j][t][m] = var
                        self.stats['variables'] += 1

    def create_register_bits_for_block(self, block_id, job, start, end):
        """Create (or reuse) register bits for a block.
        Returns (y_vars, x_vars) where y_vars has length max(len(x_vars)-1, 0).
        y_i corresponds to prefix up to x_{i+1} inside this block.
        """
        if block_id in self.register_bits:
            return self.register_bits[block_id]

        x_vars = []
        y_vars = []
        for t in range(start, end):
            if t in self.s_vars[job]:
                x_vars.append(self.s_vars[job][t])
        # allocate auxiliary y for each prefix beyond the first x
        if len(x_vars) >= 2:
            for j in range(1, len(x_vars)):
                y = self.vpool.id(f'R_{block_id}_{j}')
                y_vars.append(y)
                self.stats['register_bits'] += 1
        self.register_bits[block_id] = (y_vars, x_vars)
        return y_vars, x_vars

    def encode_amo_block(self, block_id, job, start, end):
        """Encode AMO for x_vars in [start,end) using ladder with y_vars (idempotent)."""
        if block_id in self.encoded_blocks:
            return
        y_vars, x_vars = self.create_register_bits_for_block(block_id, job, start, end)
        k = len(x_vars)
        if k <= 1:
            self.encoded_blocks.add(block_id)
            return
        # y_i is prefix up to x_{i+1}
        # Clause set:
        # 1) (¬x_1 ∨ y_1)
        self.cnf.append([-x_vars[0], y_vars[0]])
        self.stats['clauses'] += 1

        # 2) For j=2..k-1: (¬x_j ∨ y_j)
        for j in range(1, k - 1):
            self.cnf.append([-x_vars[j], y_vars[j]])
            self.stats['clauses'] += 1

        # 3) for j=1..k-2: (¬y_j ∨ y_{j+1})
        for j in range(0, k - 2):
            self.cnf.append([-y_vars[j], y_vars[j + 1]])
            self.stats['clauses'] += 1

        # 4) for j=2..k: (¬x_j ∨ ¬y_{j-1})
        for j in range(1, k):
            self.cnf.append([-x_vars[j], -y_vars[j - 1]])
            self.stats['clauses'] += 1

    def encode_amz_block(self, block_id, job, start, end):
        """Encode AMZ block (no formula 4); idempotent by block_id"""
        if block_id in self.encoded_blocks:
            return
        register_bits, block_vars = self.create_register_bits_for_block(block_id, job, start, end)
        if len(block_vars) <= 1:
            self.encoded_blocks.add(block_id)
            return

        # Formula (1): x_{i,j} → R_{i,j}
        for j in range(1, len(block_vars)):
            self.cnf.append([-block_vars[j], register_bits[j]])
            self.stats['clauses'] += 1

        # Formula (2): R_{i,j-1} → R_{i,j}
        for j in range(1, len(block_vars)):
            self.cnf.append([-register_bits[j - 1], register_bits[j]])
            self.stats['clauses'] += 1

        # Formula (3): ¬x_{i,j} ∧ ¬R_{i,j-1} → ¬R_{i,j}
        for j in range(1, len(block_vars)):
            self.cnf.append([block_vars[j], register_bits[j - 1], -register_bits[j]])
            self.stats['clauses'] += 1

        # NO Formula (4) for AMZ

    def connect_blocks(self, block1_id, block2_id):
        """Connect consecutive blocks (forward carry).
        Ensure y2_1 receives carry from y1_last; and boundary AMO across blocks.
        Idempotent via self.connected_pairs.
        """
        if block1_id not in self.register_bits or block2_id not in self.register_bits:
            return
        pair = (block1_id, block2_id)
        if pair in self.connected_pairs:
            return
        self.connected_pairs.add(pair)
        y1, x1 = self.register_bits[block1_id]
        y2, x2 = self.register_bits[block2_id]
        if not x1 or not x2:
            return
        # forward carry only if both blocks have y's available
        if y1 and y2:
            # (¬y1_last ∨ y2_1)
            self.cnf.append([-y1[-1], y2[0]])
            self.stats['connection_clauses'] += 1
        if y1:
            # boundary AMO for first var of next block: (¬x2_1 ∨ ¬y1_last)
            self.cnf.append([-x2[0], -y1[-1]])
            self.stats['connection_clauses'] += 1
        # no further per-index pairings needed; internal monotone handles rest

    def add_start_time_constraints(self):
        """Exactly one start time for each job using SCAMO blocks"""
        for j in range(1, self.jobs + 1):
            # At least one start time (ALO)
            vars_list = [self.s_vars[j][t] for t in range(self.ES[j], self.LS[j] + 1) if t in self.s_vars[j]]
            if vars_list:
                self.cnf.append(vars_list)
                self.stats['clauses'] += 1

            # Build & encode blocks
            blocks = self.create_blocks_for_job(j)
            for (block_id, start, end, _bt, _a, _b) in blocks:
                self.encode_amo_block(block_id, j, start, end)

            # Connect consecutive blocks once
            for i in range(len(blocks) - 1):
                self.connect_blocks(blocks[i][0], blocks[i + 1][0])

    def add_mode_selection_constraints(self):
        for j in range(1, self.jobs + 1):
            mode_vars = [self.sm_vars[j][m] for m in range(len(self.job_modes[j]))]
            if len(mode_vars) <= 1:
                continue
            # ALO (≥1) – CNF trực tiếp
            self.cnf.append(mode_vars)
            # AMO (≤1) – SR
            self._add_pb_via_savilerow([(mode_vars, [1] * len(mode_vars), 1)])

    def add_precedence_constraints_with_blocks(self):
        """
        Precedence per-edge blocks:
        For (pred->succ), if pred starts at t with mode m (dur=d),
        forbid succ start times ≤ t+d-1 using the AMO register bits of
        the blocks created specifically for (pred, succ).
        """
        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence:
                continue
            for succ in self.precedence[pred]:
                # Lấy từ cache hoặc build 1 lần (encode + connect đã nằm trong helper)
                blocks = self.get_or_build_precedence_blocks(pred, succ)
                if not blocks:
                    continue

                # 3) Dùng các block này để "cấm prefix ≤ thr" như cũ
                for m_pred, mode in enumerate(self.job_modes[pred]):
                    dur = mode[0]
                    for t_pred in range(self.ES[pred], self.LS[pred] + 1):
                        if t_pred not in self.s_vars[pred]:
                            continue
                        thr = t_pred + dur - 1
                        if thr < self.ES[succ]:
                            continue

                        # (1) Cấm toàn bộ block hoàn toàn <= thr
                        for (bid, st, en, _bt, _a, _b) in blocks:
                            last_t = en - 1
                            if last_t <= thr and st <= last_t:
                                y, x = self.create_register_bits_for_block(bid, succ, st, en)
                                k = len(x)
                                if k == 1:
                                    self.cnf.append([-self.sm_vars[pred][m_pred],
                                                     -self.s_vars[pred][t_pred],
                                                     -x[0]])
                                    self.stats['clauses'] += 1
                                elif k >= 2:
                                    # (¬sm ∨ ¬s_pred_t ∨ ¬y[k-2]), (¬sm ∨ ¬s_pred_t ∨ ¬x[k-1])
                                    self.cnf.append([-self.sm_vars[pred][m_pred],
                                                     -self.s_vars[pred][t_pred],
                                                     -y[k - 2]])
                                    self.cnf.append([-self.sm_vars[pred][m_pred],
                                                     -self.s_vars[pred][t_pred],
                                                     -x[k - 1]])
                                    self.stats['clauses'] += 2

                        # (2) Cấm phần prefix trong block chứa thr
                        for (bid, st, en, _bt, _a, _b) in blocks:
                            if st <= thr < en:
                                y, x = self.create_register_bits_for_block(bid, succ, st, en)
                                k = len(x)
                                idx = thr - st
                                if idx == 0:
                                    self.cnf.append([-self.sm_vars[pred][m_pred],
                                                     -self.s_vars[pred][t_pred],
                                                     -x[0]])
                                    self.stats['clauses'] += 1
                                elif idx < k - 1:
                                    self.cnf.append([-self.sm_vars[pred][m_pred],
                                                     -self.s_vars[pred][t_pred],
                                                     -y[idx]])
                                    self.stats['clauses'] += 1
                                else:  # idx == k-1
                                    if k == 1:
                                        self.cnf.append([-self.sm_vars[pred][m_pred],
                                                         -self.s_vars[pred][t_pred],
                                                         -x[0]])
                                        self.stats['clauses'] += 1
                                    else:
                                        self.cnf.append([-self.sm_vars[pred][m_pred],
                                                         -self.s_vars[pred][t_pred],
                                                         -y[k - 2]])
                                        self.cnf.append([-self.sm_vars[pred][m_pred],
                                                         -self.s_vars[pred][t_pred],
                                                         -x[k - 1]])
                                        self.stats['clauses'] += 2
                                break  # chỉ 1 block chứa thr

    def add_process_variable_constraints(self, time_limit=None):
        """Define process variables"""
        Tmax = (time_limit if time_limit is not None else self.horizon + 1)

        for j in range(1, self.jobs + 1):
            for t in range(Tmax):
                for m in range(len(self.job_modes[j])):
                    if m not in self.u_vars[j][t]:
                        continue

                    duration = self.job_modes[j][m][0]
                    valid_starts = []

                    for t_start in range(max(self.ES[j], t - duration + 1),
                                         min(self.LS[j] + 1, t + 1)):
                        if t_start in self.s_vars[j] and t_start + duration > t:
                            valid_starts.append(self.s_vars[j][t_start])

                    if valid_starts:
                        # u implies mode
                        self.cnf.append([-self.u_vars[j][t][m], self.sm_vars[j][m]])
                        self.stats['clauses'] += 1

                        # u implies at least one valid start
                        self.cnf.append([-self.u_vars[j][t][m]] + valid_starts)
                        self.stats['clauses'] += 1

                        # mode and start implies u
                        for start_var in valid_starts:
                            self.cnf.append([
                                -self.sm_vars[j][m],
                                -start_var,
                                self.u_vars[j][t][m]
                            ])
                            self.stats['clauses'] += 1
                    else:
                        self.cnf.append([-self.u_vars[j][t][m]])
                        self.stats['clauses'] += 1

    def add_renewable_resource_constraints(self):
        clause_before = len(self.cnf.clauses)
        pb_bucket = []  # gom PB để batch

        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
                lits, weights = [], []
                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        if m in self.u_vars[j][t]:
                            if len(self.job_modes[j][m][1]) > k:
                                req = self.job_modes[j][m][1][k]
                                if req > 0:
                                    lits.append(self.u_vars[j][t][m])
                                    weights.append(req)
                if lits:
                    pb_bucket.append((lits, weights, self.R_capacity[k]))

        # Gọi SR 1–vài lần
        self._add_pb_via_savilerow(pb_bucket, batch_size=1500, max_workers=8)

        clauses_after = len(self.cnf.clauses)
        print(f"Số clauses sinh ra từ add_renewable_resource_constraints (qua SR): {clauses_after - clause_before}")

    def add_nonrenewable_resource_constraints(self):
        clause_before = len(self.cnf.clauses)
        pb_bucket = []

        for k in range(self.nonrenewable_resources):
            idx = self.renewable_resources + k
            mins_per_job = {}
            for j in range(1, self.jobs + 1):
                vals = []
                for m in range(len(self.job_modes[j])):
                    vec = self.job_modes[j][m][1]
                    v = vec[idx] if len(vec) > idx else 0
                    vals.append(0 if v is None else int(v))
                mins_per_job[j] = min(vals) if vals else 0

            sum_min = sum(mins_per_job.values())
            Bk = self.N_capacity[k]  # chú ý đúng tên biến của bạn
            Bk_prime = Bk - sum_min

            if Bk_prime >= 0:
                # EO reduction: sum_j sum_m delta_{jm} * sm_{jm} <= Bk'
                lits, weights = [], []
                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        vec = self.job_modes[j][m][1]
                        v = vec[idx] if len(vec) > idx else 0
                        delta = max(0, int(v) - mins_per_job[j])
                        if delta > 0:
                            lits.append(self.sm_vars[j][m])
                            weights.append(delta)
                if lits:
                    pb_bucket.append((lits, weights, Bk_prime))
            else:
                # Fallback: sum_j sum_m b_{jm} * sm_{jm} <= Bk
                lits, weights = [], []
                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        vec = self.job_modes[j][m][1]
                        v = vec[idx] if len(vec) > idx else 0
                        if int(v) > 0:
                            lits.append(self.sm_vars[j][m])
                            weights.append(int(v))
                if lits:
                    pb_bucket.append((lits, weights, Bk))

        self._add_pb_via_savilerow(pb_bucket, batch_size=1500, max_workers=8)

        clauses_after = len(self.cnf.clauses)
        print(f"Số clauses sinh ra từ add_nonrenewable_resource_constraints (qua SR): {clauses_after - clause_before}")

    def add_makespan_constraint(self, makespan):
        """Makespan constraint"""
        sink_job = self.jobs

        for t in range(makespan + 1, self.LS[sink_job] + 1):
            if t in self.s_vars[sink_job]:
                self.cnf.append([-self.s_vars[sink_job][t]])
                self.stats['clauses'] += 1

    def encode(self, makespan=None):
        """Encode và cập nhật last_var_count/last_clause_count để ghi CSV"""
        self.create_variables()
        self.add_start_time_constraints()
        self.add_mode_selection_constraints()
        self.add_precedence_constraints_with_blocks()
        self.add_process_variable_constraints()
        self.add_renewable_resource_constraints()
        self.add_nonrenewable_resource_constraints()
        if makespan is not None:
            self.add_makespan_constraint(makespan)
        # cập nhật đếm biến/mệnh đề
        self.stats['clauses'] = len(self.cnf.clauses)
        self.last_clause_count = self.stats['clauses']
        self.last_var_count = self.vpool.top if hasattr(self.vpool, 'top') else getattr(self.vpool, '_top', 0)
        return self.cnf

    def solve(self, makespan):
        """Solve with given makespan"""
        print(f"\n--- Solving with makespan = {makespan} ---")

        # Reset
        self.cnf = CNF()
        self.vpool = IDPool()
        self.precedence_blocks = {}
        self.job_blocks = {}
        self.register_bits = {}
        self.block_connections = []

        self.stats = {
            'variables': 0,
            'clauses': 0,
            'register_bits': 0,
            'connection_clauses': 0,
        }
        self.encoded_blocks = set()
        self.connected_pairs = set()

        # Encode
        self.encode(makespan)

        # Solve
        print("Solving SAT instance...")
        solver = Glucose42()
        solver.append_formula(self.cnf)

        start_time = time.time()
        result = solver.solve()
        solve_time = time.time() - start_time

        print(f"Solve time: {solve_time:.2f}s")

        if result:
            return self.extract_solution(solver.get_model())
        else:
            return None

    def extract_solution(self, model):
        """Extract solution from SAT model"""
        solution = {}

        for j in range(1, self.jobs + 1):
            # Find start time
            start_time = None
            for t in range(self.ES[j], self.LS[j] + 1):
                if t in self.s_vars[j] and self.s_vars[j][t] <= len(model) and model[self.s_vars[j][t] - 1] > 0:
                    start_time = t
                    break

            # Find mode
            mode = None
            for m in range(len(self.job_modes[j])):
                if self.sm_vars[j][m] <= len(model) and model[self.sm_vars[j][m] - 1] > 0:
                    mode = m
                    break

            if start_time is not None and mode is not None:
                duration = self.job_modes[j][mode][0]
                resources = self.job_modes[j][mode][1]
                solution[j] = {
                    'mode': mode,
                    'start_time': start_time,
                    'duration': duration,
                    'finish_time': start_time + duration,
                    'resources': resources
                }

        return solution

    def find_optimal_makespan(self):
        """Find optimal makespan using binary search"""
        min_makespan = self.calculate_critical_path_bound()
        max_makespan = self.horizon

        best_makespan = None
        best_solution = None

        print(f"\n=== SEARCHING FOR OPTIMAL MAKESPAN ===")
        print(f"Search range: [{min_makespan}, {max_makespan}]")

        while min_makespan <= max_makespan:
            mid = (min_makespan + max_makespan) // 2

            solution = self.solve(mid)

            if solution:
                best_makespan = mid
                best_solution = solution
                max_makespan = mid - 1
                print(f"Found solution with makespan {mid}, searching for better...")
            else:
                min_makespan = mid + 1
                print(f"No solution with makespan {mid}, increasing bound...")

        return best_makespan, best_solution

    def calculate_critical_path_bound(self):
        """Calculate critical path lower bound"""
        critical_length = {}

        def get_critical_length(j):
            if j in critical_length:
                return critical_length[j]

            if j not in self.precedence or not self.precedence[j]:
                if j in self.job_modes and self.job_modes[j]:
                    critical_length[j] = min(mode[0] for mode in self.job_modes[j])
                else:
                    critical_length[j] = 0
                return critical_length[j]

            max_path = 0
            for succ in self.precedence[j]:
                path_length = get_critical_length(succ)
                max_path = max(max_path, path_length)

            if j in self.job_modes and self.job_modes[j]:
                min_duration = min(mode[0] for mode in self.job_modes[j])
            else:
                min_duration = 0

            critical_length[j] = min_duration + max_path
            return critical_length[j]

        critical_path = get_critical_length(1)
        return max(critical_path, self.ES[self.jobs] if self.jobs in self.ES else 1)

    def print_solution(self, solution, makespan):
        """Print solution details"""
        print(f"\n=== SOLUTION ===")
        print(f"Makespan: {makespan}")
        print(f"\n{'Job':<5} {'Mode':<6} {'Start':<7} {'Duration':<10} {'Finish':<8} {'Resources':<20}")
        print("-" * 65)

        for j in sorted(solution.keys()):
            info = solution[j]
            res_str = ' '.join(f"{r:2d}" for r in info['resources'])
            print(f"{j:<5} {info['mode'] + 1:<6} {info['start_time']:<7} "
                  f"{info['duration']:<10} {info['finish_time']:<8} "
                  f"{res_str:<20}")

    def validate_solution(self, solution):
        """Validate the solution"""
        print("\n=== VALIDATING SOLUTION ===")
        valid = True

        # Get actual makespan
        actual_makespan = max(s['finish_time'] for s in solution.values())
        print(f"Actual makespan from solution: {actual_makespan}")

        # Check precedence constraints
        print("\nChecking precedence constraints...")
        precedence_ok = True
        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence or pred not in solution:
                continue

            for succ in self.precedence[pred]:
                if succ not in solution:
                    continue

                if solution[pred]['finish_time'] > solution[succ]['start_time']:
                    print(f"  ✗ Precedence violated: Job {pred} finishes at {solution[pred]['finish_time']}, "
                          f"but Job {succ} starts at {solution[succ]['start_time']}")
                    valid = False
                    precedence_ok = False

        if precedence_ok:
            print("  ✓ All precedence constraints satisfied")

        # Check renewable resources
        print("\nChecking renewable resource constraints...")
        renewable_ok = True
        for k in range(self.renewable_resources):
            for t in range(actual_makespan + 1):
                usage = 0
                for j, info in solution.items():
                    if info['start_time'] <= t < info['finish_time']:
                        if len(info['resources']) > k:
                            usage += info['resources'][k]

                if usage > self.R_capacity[k]:
                    print(f"  ✗ Renewable resource {k + 1} violated at time {t}: "
                          f"usage={usage} > capacity={self.R_capacity[k]}")
                    valid = False
                    renewable_ok = False
                    break

        if renewable_ok:
            print("  ✓ All renewable resource constraints satisfied")

        # Check non-renewable resources
        print("\nChecking non-renewable resource constraints...")
        nonrenewable_ok = True
        for k in range(self.nonrenewable_resources):
            total_usage = 0
            for j, info in solution.items():
                resource_idx = self.renewable_resources + k
                if len(info['resources']) > resource_idx:
                    total_usage += info['resources'][resource_idx]

            if total_usage > self.N_capacity[k]:
                print(f"  ✗ Non-renewable resource {k + 1} violated: "
                      f"total usage={total_usage} > capacity={self.N_capacity[k]}")
                valid = False
                nonrenewable_ok = False

        if nonrenewable_ok:
            print("  ✓ All non-renewable resource constraints satisfied")

        if valid:
            print("\n✓ Solution is VALID!")
        else:
            print("\n✗ Solution is INVALID!")

        return valid

    def _add_pb_via_savilerow(
            self,
            pb_list: list[tuple[list[int], list[int], int]],
            batch_size: int = 2400,
            tmp_dir: str = "sr_tmp",
            savilerow_bin: str = "savilerow-1.10.1-linux",
            keep_tmp: bool = False,
            max_workers: int | None = None,
    ):
        """
        Parallel SR:
          1) Chia pb_list thành các batch.
          2) Chạy Savile Row cho từng batch SONG SONG (thread pool), nhận .dimacs.
          3) Parse DIMACS và append vào self.cnf TUẦN TỰ để an toàn vpool.
          4) Dọn rác từng batch_dir sau khi parse (nếu keep_tmp=False).
        """
        if not pb_list:
            return

        os.makedirs(tmp_dir, exist_ok=True)
        # 1) Chia batch
        batches = [pb_list[i:i + batch_size] for i in range(0, len(pb_list), batch_size)]
        if not batches:
            return

        workers = _safe_workers(max_workers)

        # 2) Chạy SR song song để tạo DIMACS
        results = []  # giữ kết quả theo thứ tự gửi đi để reproducible
        with ThreadPoolExecutor(max_workers=workers) as ex:
            futures = []
            for b in batches:
                fut = ex.submit(_run_sr_batch, b, tmp_dir, savilerow_bin)
                futures.append(fut)
            # Thu kết quả *theo đúng thứ tự nộp* (không dùng as_completed để giữ determinism)
            for fut in futures:
                batch_dir, dimacs = fut.result()
                results.append((batch_dir, dimacs))

        # 3) Parse DIMACS tuần tự (an toàn cho vpool) + 4) cleanup
        try:
            for (batch_dir, dimacs_path) in results:
                cls = _sr_parse_dimacs_to_cnf(dimacs_path, self.vpool)
                if cls:
                    self.cnf.extend(cls)
            if hasattr(self, "stats"):
                self.stats["clauses"] = len(self.cnf.clauses)
        finally:
            if not keep_tmp:
                for (batch_dir, _dimacs_path) in results:
                    try:
                        shutil.rmtree(batch_dir, ignore_errors=True)
                    except Exception:
                        pass

# ==========================
#  Hàm tiện ích đọc .mm
# ==========================
def load_reader(mm_path):
    from MRCPSP_SCAMO_MMLIB import MMLIB50Reader  # dùng reader cho MMLIB
    return MMLIB50Reader(str(mm_path))

def compute_lb_energetic(data):
    """
    LB = max( LB_crit(d_min), max_k ceil( sum_j min_m d_{jm} * r_{jmk} / C_k ) )
    data: dict với các khóa như encoder dùng (num_jobs, num_renewable, ...).
    """
    J = data['num_jobs']
    R = data['num_renewable']
    C = data['renewable_capacity']
    modes = data['job_modes']
    prec = data['precedence']

    # 1) Critical path bound với d_min
    dmin = {j: min(d for d, _ in modes[j]) for j in range(1, J+1)}
    from collections import deque
    succ = {i: set(prec.get(i, [])) for i in range(1, J+1)}
    indeg = {i: 0 for i in range(1, J+1)}
    for u, vs in succ.items():
        for v in vs:
            indeg[v] += 1
    q = deque([i for i in range(1, J+1) if indeg[i] == 0])
    topo = []
    while q:
        u = q.popleft()
        topo.append(u)
        for v in succ[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    ES = {j: 0 for j in range(1, J+1)}
    for u in topo:
        for v in succ[u]:
            ES[v] = max(ES[v], ES[u] + dmin[u])
    LB_crit = max((ES[u] + dmin[u] for u in topo), default=0)

    # 2) Energetic bound cho renewables
    LB_R = 0
    for k in range(R):
        Ek = 0
        for j in range(1, J+1):
            Ek += min(d * (req[k] if k < len(req) else 0) for d, req in modes[j])
        cap = C[k]
        if cap > 0:
            LB_R = max(LB_R, (Ek + cap - 1) // cap)  # ceil
    return max(LB_crit, LB_R)

def compute_ub_ssgs(mm_reader, restarts, seed):
    """
    Trả về UB khả thi bằng SSGS (không dùng horizon của .mm).
    UB = max finish_time của lịch tốt nhất trong 'restarts' lần.
    """
    import random
    rng = random.Random(seed)

    jobs = mm_reader.data['num_jobs']
    R = mm_reader.data['num_renewable']
    NR = mm_reader.data['num_nonrenewable']
    Rcap = mm_reader.data['renewable_capacity']
    Ncap = mm_reader.data['nonrenewable_capacity']
    prec = mm_reader.data['precedence']
    modes = mm_reader.data['job_modes']

    # topo order
    succ = {i: set(prec.get(i, [])) for i in range(1, jobs+1)}
    preds = {i: set() for i in range(1, jobs+1)}
    for u, Vs in succ.items():
        for v in Vs: preds[v].add(u)
    from collections import deque
    q = deque([i for i in range(1, jobs+1) if not preds[i]])
    topo = []
    indeg = {i: len(preds[i]) for i in preds}
    while q:
        u = q.popleft(); topo.append(u)
        for v in succ[u]:
            indeg[v] -= 1
            if indeg[v] == 0: q.append(v)

    # tiện ích: earliest feasible t trên profile R (tự giãn)
    def earliest_feasible_start(dur, reqR, est, Rprof):
        t = est
        while True:
            need_len = t + dur
            for k in range(R):
                if len(Rprof[k]) < need_len:
                    Rprof[k].extend([Rcap[k]] * (need_len - len(Rprof[k])))
            ok = True
            for tau in range(t, t+dur):
                for k in range(R):
                    need = reqR[k] if k < len(reqR) else 0
                    if need and Rprof[k][tau] < need:
                        ok = False; break
                if not ok: break
            if ok: return t
            t += 1

    # chọn mode “dễ xếp”: (dur ↑, dùng R/N thấp) nhưng không vượt N còn lại
    def pick_mode(j, Nrem):
        best = None
        for m,(dur,req) in enumerate(modes[j]):
            # check non-renewable
            ok = True
            for kk in range(NR):
                idx = R + kk
                need = req[idx] if idx < len(req) else 0
                if need > Nrem[kk]: ok=False; break
            if not ok: continue
            rsum = sum((req[k] if k < R else 0) for k in range(R))
            nsum = sum((req[R+kk] if R+kk < len(req) else 0) for kk in range(NR))
            key = (dur, rsum, nsum, m)   # ưu tiên dur nhỏ, dùng R/N nhỏ
            if best is None or key < best[0]:
                best = (key, m, dur, req)
        return best

    best = None
    for _ in range(restarts):
        # shuffle nhẹ trong các nhóm successor-similar để đa dạng
        order = topo[:]
        i = 0
        while i < len(order):
            j = i
            while j+1 < len(order) and len(succ[order[j+1]]) == len(succ[order[i]]):
                j += 1
            block = order[i:j+1]
            rng.shuffle(block)
            order[i:j+1] = block
            i = j+1

        # khởi tạo profile
        Rprof = [[Rcap[k]] for k in range(R)]
        Nrem  = [Ncap[kk] for kk in range(NR)]
        start, finish = {}, {}

        feasible = True
        for j in order:
            est = 0
            for p in preds[j]:
                if p in finish: est = max(est, finish[p])

            pick = pick_mode(j, Nrem)
            if pick is None: feasible = False; break
            _, m, dur, req = pick
            reqR = [ (req[k] if k < R else 0) for k in range(R) ]
            reqN = [ (req[R+kk] if R+kk < len(req) else 0) for kk in range(NR) ]

            t = earliest_feasible_start(dur, reqR, est, Rprof)

            # cập nhật profile
            for tau in range(t, t+dur):
                for k in range(R):
                    need = reqR[k]
                    if need: Rprof[k][tau] -= need
            for kk in range(NR):
                Nrem[kk] -= reqN[kk]
                if Nrem[kk] < 0: feasible = False; break
            if not feasible: break

            start[j] = t; finish[j] = t + dur

        if feasible:
            mk = max(finish.values()) if finish else 0
            best = mk if best is None else min(best, mk)

    if best is None:
        # fallback siêu an toàn: xếp nối chuỗi theo min duration
        mk = 0
        for j in topo:
            dmin = min(d for d,_ in modes[j])
            mk += dmin
        best = mk

    return best

def _safe_workers(n):
    try:
        cpu = os.cpu_count() or 1
    except Exception:
        cpu = 1
    # mặc định: tận dụng ~1/2 số core, tối đa 8
    return max(1, min(8, n if n else max(1, cpu // 2)))

def _run_sr_batch(batch, base_tmp_dir, savilerow_bin):
    """
    Chạy 1 batch Savile Row trong thư mục tạm riêng.
    Trả về (batch_dir, dimacs_path). Không parse ở đây để tránh đụng vpool.
    """
    batch_dir = tempfile.mkdtemp(prefix="sr_batch_", dir=base_tmp_dir)
    eprime = _sr_create_eprime_from_pbs(batch, batch_dir)
    dimacs = _sr_run_and_get_dimacs(eprime, batch_dir, savilerow_bin=savilerow_bin)
    return batch_dir, dimacs  # cleanup sau khi parse

def _sr_create_eprime_from_pbs(pbs, out_dir: str) -> str:
    """
    pbs: list of (lits, weights, bound) cho ràng buộc sum(w_i * toInt(x_lit_i)) <= bound
    """
    os.makedirs(out_dir, exist_ok=True)
    eprime_path = os.path.join(out_dir, f"pb_{uuid.uuid4().hex}.eprime")

    constraints = []
    used = set()

    for lits, weights, bound in pbs:
        if not lits:
            continue
        # nếu tổng trọng số <= bound, ràng buộc vô hiệu -> bỏ
        if sum(weights) <= bound:
            continue
        used.update(lits)
        terms = [f"{w}*toInt(x{l})" for l, w in zip(lits, weights) if w]
        if terms:
            constraints.append(f"{' + '.join(terms)} <= {bound}")

    with open(eprime_path, "w") as f:
        f.write("language ESSENCE' 1.0\n")
        # Khai báo biến bool; có thể gộp hoặc mỗi dòng 1 biến, đều được
        for l in sorted(used):
            f.write(f"find x{l} : bool\n")
        f.write("such that\n")
        if constraints:
            # Dùng danh sách ràng buộc, ngăn cách bằng dấu phẩy (cú pháp Essence’ chuẩn)
            f.write(",\n".join(constraints))
        else:
            f.write("true\n")

    return eprime_path

def _ensure_sr_bundle_exec(savilerow_bin: str):
    """
    Nếu savilerow_bin là thư mục bundle, tự +x cho savilerow và bin/*
    Nếu là file savilerow, tự +x file đó.
    Nếu là .jar thì bỏ qua.
    """
    sb = os.path.abspath(savilerow_bin)
    p = Path(sb)
    if p.suffix == ".jar":
        return
    try:
        if p.is_dir():
            exe = p / "savilerow"
            if exe.exists():
                st = os.stat(exe)
                os.chmod(exe, st.st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
            bin_dir = p / "bin"
            if bin_dir.exists() and bin_dir.is_dir():
                for child in bin_dir.iterdir():
                    if child.is_file():
                        st = os.stat(child)
                        os.chmod(child, st.st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
        else:
            if os.path.isfile(sb) and not os.access(sb, os.X_OK):
                st = os.stat(sb)
                os.chmod(sb, st.st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    except Exception:
        # best-effort; không chặn luồng nếu chmod fail
        pass

def _is_executable_file(p: str) -> bool:
    return os.path.isfile(p) and os.access(p, os.X_OK)

def _sr_run_and_get_dimacs(eprime_path: str, out_dir: str, savilerow_bin: str = "savilerow-1.10.1-linux") -> str:
    """
    Chạy Savile Row để xuất DIMACS; in ra thông báo lỗi nếu fail.
    """
    _ensure_sr_bundle_exec(savilerow_bin)
    os.makedirs(out_dir, exist_ok=True)
    dimacs_path = os.path.join(out_dir, f"{Path(eprime_path).stem}.dimacs")

    def _run(cmd_list):
        # SR_DEBUG: nếu đặt SR_DEBUG=1 sẽ không nuốt log
        if os.environ.get("SR_DEBUG") == "1":
            proc = subprocess.run(cmd_list, text=True)
            if proc.returncode != 0:
                raise subprocess.CalledProcessError(proc.returncode, cmd_list)
        else:
            proc = subprocess.run(cmd_list, capture_output=True, text=True)
            if proc.returncode != 0:
                msg = []
                msg.append("Savile Row failed.")
                msg.append(f"Command: {' '.join(cmd_list)}")
                msg.append(f"STDOUT:\n{proc.stdout.strip()}")
                msg.append(f"STDERR:\n{proc.stderr.strip()}")
                raise RuntimeError("\n".join(msg))

    sb = os.path.abspath(savilerow_bin)
    p = Path(sb)

    # Nếu là folder -> thử savilerow, rồi savilerow.jar
    candidates = []
    if p.is_dir():
        candidates = [str(p / "savilerow"), str(p / "savilerow.jar")]
    else:
        candidates = [sb]

    last_err = None
    for cand in candidates:
        try:
            if cand.endswith(".jar") and os.path.isfile(cand):
                java = shutil.which("java") or "java"
                _run([java, "-Xmx2G", "-jar", cand, eprime_path, "-sat", "-sat-pb-mdd", "-amo-detect", "-out-sat", dimacs_path])
                return dimacs_path

            if os.path.isfile(cand) and not os.access(cand, os.X_OK):
                st = os.stat(cand)
                os.chmod(cand, st.st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)

            if os.path.isfile(cand) and os.access(cand, os.X_OK):
                _run([cand, eprime_path, "-sat", "-sat-pb-mdd", "-amo-detect", "-out-sat", dimacs_path])
                return dimacs_path
        except Exception as e:
            last_err = e
            continue

    if last_err:
        raise last_err
    raise FileNotFoundError(f"Cannot locate runnable Savile Row at: {savilerow_bin}")

def _sr_parse_dimacs_to_cnf(dimacs_path: str, vpool) -> list[list[int]]:
    """
    Đọc DIMACS và map biến 'xK' (từ comment 'c Encoding variable: xK') về literal gốc K.
    Biến phụ do SR sinh sẽ được cấp id mới từ vpool.id().
    Trả về list các mệnh đề (list[int]).
    """
    clauses = []
    litmap = {}   # DIMACS var id -> original literal K
    auxmap = {}   # DIMACS var id -> new id from vpool

    with open(dimacs_path, "r") as f:
        for line in f:
            if not line.strip() or line[0] == 'p':
                continue
            if line.startswith("c Encoding variable:"):
                # dòng sau thường chứa id DIMACS tương ứng
                var_match = re.search(r'x(\d+)', line)
                sat_line = next(f, "")
                sat_match = re.search(r'(\d+)', sat_line)
                if var_match and sat_match:
                    litmap[int(sat_match.group(1))] = int(var_match.group(1))
                continue
            if line[0] == 'c':
                continue
            # mệnh đề
            nums = [int(x) for x in line.split()]
            if not nums:
                continue
            cl = []
            for v in nums:
                if v == 0:
                    break
                av = abs(v)
                if av in litmap:
                    g = litmap[av]
                else:
                    # biến phụ
                    if av not in auxmap:
                        auxmap[av] = vpool.id()
                    g = auxmap[av]
                cl.append(g if v > 0 else -g)
            if cl:
                clauses.append(cl)

    return clauses

# ==========================
#  Giải 1 instance với timeout & nhị phân makespan
# ==========================
def _atomic_dump_json(path: Path, payload: dict):
    tmp = Path(str(path) + ".tmp")
    tmp.parent.mkdir(parents=True, exist_ok=True)
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)  # atomic rename

def solve_instance_with_timeout(mm_path, timeout_s=2400, checkpoint_path: Path | None = None):
    reader = load_reader(mm_path)
    enc = MRCPSPBlockBasedStaircase(reader)

    data_for_lb = {
        'num_jobs': enc.jobs,
        'num_renewable': enc.renewable_resources,
        'num_nonrenewable': enc.nonrenewable_resources,
        'renewable_capacity': enc.R_capacity,
        'nonrenewable_capacity': enc.N_capacity,
        'precedence': enc.precedence,
        'job_modes': enc.job_modes,
    }

    # LB cơ bản (CPM) + nâng bằng energetic LB
    lb_cpm = enc.calculate_critical_path_bound()
    lb_energy = compute_lb_energetic(data_for_lb)
    lb = max(lb_cpm, lb_energy)

    # UB khởi tạo
    ub_ssgs = compute_ub_ssgs(reader, restarts=16, seed=4000)
    ub = min(reader.get_horizon(), ub_ssgs)

    start = time.time()
    timeout_flag = False
    best_makespan = None
    best_vars = 0
    best_clauses = 0

    lo, hi = lb, ub
    while lo <= hi:
        if time.time() - start > timeout_s:
            timeout_flag = True
            break

        mid = (lo + hi) // 2

        # Quick filter: nếu mid < energetic LB => chắc chắn infeasible, skip SAT
        if mid < lb_energy:
            lo = mid + 1
            continue

        solution = enc.solve(mid)

        if time.time() - start > timeout_s:
            timeout_flag = True

        if solution:
            # cập nhật best-so-far
            best_makespan = mid
            best_vars = enc.last_var_count
            best_clauses = enc.last_clause_count
            # nếu đã bằng LB thì tối ưu luôn, thoát sớm
            if mid == lb:
                break
            hi = mid - 1

            # ghi checkpoint ngay khi có nghiệm mới
            if checkpoint_path is not None:
                _atomic_dump_json(checkpoint_path, {
                    "instance": Path(mm_path).name,
                    "horizon": ub,
                    "variables": best_vars,
                    "clauses": best_clauses,
                    "makespan": best_makespan,
                    "status": "Feasible",
                    "Solve time": f"{time.time()-start:.2f}",
                    "timeout": "No",
                    "error": ""
                })
        else:
            lo = mid + 1

        if timeout_flag:
            break

    total_time = time.time() - start
    if timeout_flag:
        status = "Feasible"  # theo yêu cầu của bạn
    else:
        status = "Optimal" if best_makespan is not None else "Infeasible"

    row = {
        "instance": Path(mm_path).name,
        "horizon": ub,
        "variables": best_vars if best_makespan is not None else enc.last_var_count,
        "clauses": best_clauses if best_makespan is not None else enc.last_clause_count,
        "makespan": best_makespan if best_makespan is not None else "",
        "status": status,
        "Solve time": f"{total_time:.2f}",
        "timeout": "Yes" if timeout_flag else "No",
        "error": ""
    }
    return row

# ==========================
#  WORKER chế độ 1-instance (subprocess)
# ==========================
def _worker_main():
    """
    Chạy trong chế độ worker: giải đúng 1 instance rồi ghi JSON ra file --out.
    """
    import argparse, gc
    parser = argparse.ArgumentParser()
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--mm", required=True, help="Đường dẫn file .mm")
    parser.add_argument("--timeout", type=int, default=2400)
    parser.add_argument("--out", required=True, help="Đường dẫn file JSON output")
    args = parser.parse_args()

    mm_path = Path(args.mm)
    out_path = Path(args.out)

    try:
        row = solve_instance_with_timeout(mm_path, timeout_s=args.timeout, checkpoint_path=out_path)
    except Exception as e:
        tb = traceback.format_exc()
        row = {"instance": mm_path.name, "horizon": "",
               "variables": 0, "clauses": 0,
               "makespan": "", "status": "Error",
               "Solve time": "0.00", "timeout": "No",
               "error": f"{e}\n{tb}"}

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(row, f, ensure_ascii=False)
        f.flush()
        os.fsync(f.fileno())
    try:
        gc.collect()
    except Exception:
        pass

TMP_DIR = Path("tmp_results")  # chỗ chứa JSON tạm
TMP_DIR.mkdir(parents=True, exist_ok=True)

def _run_worker_for_instance(mm_path: Path, time_limit: int) -> dict:
    out_final = TMP_DIR / f"{mm_path.stem}__{uuid.uuid4().hex}.json"
    out_part  = TMP_DIR / (out_final.name + ".part")

    cmd = [
        sys.executable, "-u", __file__,
        "--worker",
        "--mm", str(mm_path),
        "--out", str(out_part),
        "--timeout", str(time_limit),
    ]

    wall = time_limit + 1
    t0 = time.time()
    # Quan trọng: không PIPE stdout để tránh treo vì đầy buffer
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.DEVNULL,          # <- tránh block do log
        stderr=subprocess.PIPE,             # giữ stderr để chẩn đoán nếu fail
        text=True,
        start_new_session=True,             # để kill theo group
    )
    try:
        _, err = proc.communicate(timeout=wall)
    except subprocess.TimeoutExpired:
        # quá hạn: kill cả group (solver con, v.v.)
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except Exception:
            proc.kill()
        try:
            proc.wait(5)
        except Exception:
            pass

        # Thử đọc checkpoint nếu có
        data = None
        if out_part.exists():
            for _ in range(10):  # retry ngắn
                try:
                    with open(out_part, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    break
                except json.JSONDecodeError:
                    time.sleep(0.1)

        if data is not None:
            data["timeout"] = "Yes"
            data["status"] = "Feasible"
            data["Solve time"] = f"{time.time() - t0:.2f}"
            data["error"] = "wall-time kill (parent)"
            return data

        # fallback nếu không có checkpoint
        return {
            "instance": mm_path.name, "horizon": "",
            "variables": 0, "clauses": 0,
            "makespan": "", "status": "Feasible",  # cũng để Feasible khi timeout
            "Solve time": f"{time.time() - t0:.2f}",
            "timeout": "Yes",
            "error": "wall-time kill (parent)"
        }

    # Worker xong: nếu có file .part thì rename atomically
    if out_part.exists():
        try:
            out_part.replace(out_final)
        except Exception:
            pass

    # Đọc JSON với retry ngắn (tránh đọc sớm)
    data = None
    for _ in range(25):  # ~2.5s
        if out_final.exists():
            try:
                with open(out_final, "r", encoding="utf-8") as f:
                    data = json.load(f)
                break
            except json.JSONDecodeError:
                time.sleep(0.1)
        else:
            time.sleep(0.1)

    if data is None:
        err_msg = (err or "").strip() if proc.returncode else "no-json"
        return {
            "instance": mm_path.name, "horizon": "",
            "variables": 0, "clauses": 0,
            "makespan": "", "status": "Error",
            "Solve time": f"{time.time()-t0:.2f}",
            "timeout": "No",
            "error": f"missing worker JSON; rc={proc.returncode}; stderr={err_msg[:500]}"
        }
    return data

# ==========================
#  GCS helpers
# ==========================
def _upload_to_gcs(bucket_name: str, local_file: Path, dest_blob: str):
    """Upload 1 file lên GCS: gs://bucket_name/dest_blob"""
    if not _GCS_AVAILABLE:
        print("google-cloud-storage chưa được cài. Bỏ qua upload.")
        return
    client = storage.Client()  # dùng ADC hoặc GOOGLE_APPLICATION_CREDENTIALS
    bucket = client.bucket(bucket_name)
    blob = bucket.blob(dest_blob)
    blob.upload_from_filename(str(local_file))
    print(f"  ☁ Uploaded to gs://{bucket_name}/{dest_blob}")

# ==========================
#  Chạy hàng loạt & ghi CSV + upload GCS
# ==========================
def run_batch_MMLIB50(
    data_dir="data/MMLIB50_remainder_1",
    out_dir="result/MMLIB50_remainder_1",
    timeout_s=2400,
    gcs_bucket: str | None = None,
    gcs_prefix: str | None = "result/MMLIB50_remainder_1",
):
    """
    Nếu gcs_bucket != None, mỗi lần ghi CSV sẽ upload file lên:
    gs://<gcs_bucket>/<gcs_prefix>/<csv_filename>
    """
    data_path = Path(data_dir)
    out_path = Path(out_dir)
    out_path.mkdir(parents=True, exist_ok=True)

    # chuẩn bị sandbox worker & file CSV
    script_path = Path(__file__).resolve()
    tmp_dir = out_path / "_tmp_worker"
    tmp_dir.mkdir(parents=True, exist_ok=True)

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    csv_file = out_path / f"MRCPSP_MMLIB50_remainder_results_{ts}.csv"

    fields = ["instance", "horizon", "variables", "clauses",
              "makespan", "status", "Solve time", "timeout", "error"]

    results = []
    mm_files = sorted(data_path.glob("*.mm"))
    print(f"Found {len(mm_files)} instances in {data_path}")

    # Ghi header ngay khi tạo file
    with csv_file.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields, extrasaction='ignore')
        writer.writeheader()

    # Upload header lên GCS
    if gcs_bucket:
        dest_blob = f"{gcs_prefix.rstrip('/')}/{csv_file.name}" if gcs_prefix else csv_file.name
        try:
            _upload_to_gcs(gcs_bucket, csv_file, dest_blob)
        except Exception as e:
            print(f"  ⚠ Không thể upload header lên GCS: {e}")

    for idx, mm in enumerate(mm_files, start=1):
        print(f"[{idx}/{len(mm_files)}] Solving {mm.name} ...")
        try:
            # CHẠY TRONG SUBPROCESS CÁCH LY RAM/exit(0)
            row = _run_worker_for_instance(mm, timeout_s)
        except Exception as e:
            print(f"  -> Error instance {mm.name}: {e}")
            row = {
                "instance": mm.name, "horizon": "", "variables": 0, "clauses": 0,
                "makespan": "", "status": "Error", "Solve time": "0.00",
                "timeout": "No", "error": "parent call error"
            }

        results.append(row)

        # Ghi theo lô mỗi 10 dòng
        if idx % 10 == 0:
            with csv_file.open("a", newline="", encoding="utf-8") as f:
                writer = csv.DictWriter(f, fieldnames=fields, extrasaction='ignore')
                writer.writerows(results[-10:])
            print(f"  ✓ Đã lưu tạm 10 dòng vào {csv_file}")

            # Upload bản cập nhật CSV lên GCS
            if gcs_bucket:
                dest_blob = f"{gcs_prefix.rstrip('/')}/{csv_file.name}" if gcs_prefix else csv_file.name
                try:
                    _upload_to_gcs(gcs_bucket, csv_file, dest_blob)
                except Exception as e:
                    print(f"  ⚠ Không thể upload batch lên GCS: {e}")

    # Ghi nốt phần còn lại (<10 cuối)
    remainder = len(results) % 10
    if remainder:
        with csv_file.open("a", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fields, extrasaction='ignore')
            writer.writerows(results[-remainder:])
        print(f"  ✓ Đã lưu phần còn lại ({remainder} dòng) vào {csv_file}")

    # Upload lần cuối
    if gcs_bucket:
        dest_blob = f"{gcs_prefix.rstrip('/')}/{csv_file.name}" if gcs_prefix else csv_file.name
        try:
            _upload_to_gcs(gcs_bucket, csv_file, dest_blob)
        except Exception as e:
            print(f"  ⚠ Không thể upload lần cuối lên GCS: {e}")

    print(f"\nHoàn tất. Kết quả lưu tại: {csv_file}")
    if gcs_bucket:
        print(f"  Và tại: gs://{gcs_bucket}/{dest_blob}")

    return csv_file

# ==========================
#  Entry point
# ==========================
if __name__ == "__main__":
    # Nếu được gọi như worker (chạy 1 instance duy nhất)
    if "--worker" in sys.argv:
        _worker_main()
        sys.exit(0)

    # Chế độ batch (cloud)
    run_batch_MMLIB50(
        data_dir="data/MMLIB50_remainder_1",
        out_dir="result/MMLIB50_remainder_1",
        timeout_s=2400,
        gcs_bucket="mrcpsp",
        gcs_prefix="result/MMLIB50_remainder_1"
    )