"""
MRCPSP Block-Based Staircase Encoding với Precedence-Aware Adaptive Width
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
import time
import math


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
                # 0 hoặc 1 mode thì không cần encode thêm
                continue
            # Exactly-One: sum(mode_vars) == 1
            pb = PBEnc.equals(lits=mode_vars,
                              weights=[1] * len(mode_vars),
                              bound=1,
                              vpool=self.vpool,
                              encoding=1)
            self.cnf.extend(pb)

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

    def add_renewable_resource_constraints(self, time_limit=None):
        """Renewable resource constraints"""
        Tmax = (time_limit if time_limit is not None else self.horizon + 1)

        clause_before = len(self.cnf.clauses)
        for k in range(self.renewable_resources):
            for t in range(Tmax):
                resource_vars = []
                resource_weights = []

                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        if m in self.u_vars[j][t]:
                            if len(self.job_modes[j][m][1]) > k:
                                resource_req = self.job_modes[j][m][1][k]
                                if resource_req > 0:
                                    resource_vars.append(self.u_vars[j][t][m])
                                    resource_weights.append(resource_req)

                if resource_vars:
                    pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                                 self.R_capacity[k], vpool=self.vpool, encoding=5)
                    self.cnf.extend(pb_constraint)

        clauses_after = len(self.cnf.clauses)  # Đếm số clauses sau khi thêm
        renewable_clauses = clauses_after - clause_before
        print(f"Số clauses sinh ra từ add_renewable_resource_constraints: {renewable_clauses}")

    def add_nonrenewable_resource_constraints(self):
        """
        Non-renewable with EO-reduction (4.4.1/3.2.5) + fallback:
          - m_i = min_o b_{iok}
          - B'_k = B_k - sum_i m_i
          - sum delta_{iok} * sm_{io} <= B'_k, where delta = max(0, b_{iok} - m_i)
          - if B'_k < 0  -> fallback to plain PB: sum b_{iok} * sm_{io} <= B_k
        """
        clause_before = len(self.cnf.clauses)
        for k in range(self.nonrenewable_resources):
            idx = self.renewable_resources + k  # cột non-renewable k trong vector yêu cầu

            # Tính m_i = min_o b_{iok} (mặc định 0 nếu job không có mode)
            mins_per_job = {}
            for j in range(1, self.jobs + 1):
                vals = []
                for m in range(len(self.job_modes[j])):
                    vec = self.job_modes[j][m][1]
                    v = vec[idx] if len(vec) > idx else 0
                    vals.append(0 if v is None else int(v))
                mins_per_job[j] = min(vals) if vals else 0

            sum_min = sum(mins_per_job.values())
            Bk = self.N_capacity[k]
            Bk_reduced = Bk - sum_min

            # Xây lists biến & trọng số theo 2 phương án
            def _plain_pb_lists():
                resource_vars, resource_weights = [], []
                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        vec = self.job_modes[j][m][1]
                        v = vec[idx] if len(vec) > idx else 0
                        v = 0 if v is None else int(v)
                        if v > 0:
                            resource_vars.append(self.sm_vars[j][m])
                            resource_weights.append(v)
                return resource_vars, resource_weights

            def _eo_pb_lists():
                resource_vars, resource_weights = [], []
                for j in range(1, self.jobs + 1):
                    m_i = mins_per_job[j]
                    for m in range(len(self.job_modes[j])):
                        vec = self.job_modes[j][m][1]
                        v = vec[idx] if len(vec) > idx else 0
                        v = 0 if v is None else int(v)
                        delta = v - m_i
                        if delta > 0:
                            resource_vars.append(self.sm_vars[j][m])
                            resource_weights.append(delta)
                return resource_vars, resource_weights

            if Bk_reduced < 0:
                # basic PB
                resource_vars, resource_weights = _plain_pb_lists()
                if resource_vars:
                    pb = PBEnc.atmost(lits=resource_vars,
                                      weights=resource_weights,
                                      bound=Bk,
                                      vpool=self.vpool,
                                      encoding=5)
                    self.cnf.extend(pb)
            else:
                # EO-reduction
                resource_vars, resource_weights = _eo_pb_lists()
                if resource_vars:
                    pb = PBEnc.atmost(lits=resource_vars,
                                      weights=resource_weights,
                                      bound=Bk_reduced,
                                      vpool=self.vpool,
                                      encoding=5)
                    self.cnf.extend(pb)

        clauses_after = len(self.cnf.clauses)  # Đếm số clauses sau khi thêm
        renewable_clauses = clauses_after - clause_before
        print(f"Số clauses sinh ra từ add_non_renewable_resource_constraints: {renewable_clauses}")

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

def run_precedence_aware_encoding(test_file=None):
    """Test the precedence-aware block encoding"""

    try:
        from MRCPSP_Basic import MRCPSPDataReader
    except:
        print("Cannot import MRCPSPDataReader")
        return None, None

    if test_file is None:
        test_file = "data/j30/j3037_1.mm"

    print("=" * 100)
    print("TESTING PRECEDENCE-AWARE BLOCK-BASED ENCODING")
    print("=" * 100)

    reader = MRCPSPDataReader(test_file)

    print(f"\nInstance: {test_file}")
    print(f"Jobs: {reader.data['num_jobs']}")
    print(f"Horizon: {reader.get_horizon()}")
    print(f"Resources: R={reader.data['renewable_capacity']}, N={reader.data['nonrenewable_capacity']}")

    # Show precedence structure
    print(f"\nPrecedence structure:")
    for j in range(1, min(reader.data['num_jobs'] + 1, 8)):  # Show first 7 jobs
        if j in reader.data['precedence'] and reader.data['precedence'][j]:
            print(f"  Job {j} → {reader.data['precedence'][j]}")

    # Create encoder with precedence-aware blocks
    encoder = MRCPSPBlockBasedStaircase(reader)

    # Find optimal makespan
    import time
    start_time = time.time()
    optimal_makespan, solution = encoder.find_optimal_makespan()
    total_time = time.time() - start_time

    if optimal_makespan and solution:
        encoder.print_solution(solution, optimal_makespan)
        encoder.validate_solution(solution)
        print(f"\n✓ Successfully found optimal makespan = {optimal_makespan}")
        print(f"Total solving time: {total_time:.2f}s")
        return optimal_makespan, total_time
    else:
        print(f"\n✗ No solution found")
        return None, None

if __name__ == "__main__":
    # Default test
    run_precedence_aware_encoding()
    print("\n" + "=" * 100)
