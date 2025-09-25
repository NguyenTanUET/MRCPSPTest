"""
MRCPSP Block-Based Staircase Encoding với Precedence-Aware Adaptive Width
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
import time
import math
# === MMLIB50 Reader (chịu REQUESTS/DURATIONS có/không có ':') ===
import os, re, uuid, subprocess, tempfile
import stat
import tempfile, shutil, os
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import subprocess
from copy import deepcopy

class MMLIB50Reader:
    def __init__(self, filename: str):
        self.filename = filename
        self.data = self._read_file()

    def _read_file(self):
        text = Path(self.filename).read_text(encoding="utf-8", errors="ignore")
        lines = [ln.rstrip() for ln in text.splitlines()]
        data, idx, n = {}, 0, len(lines)

        jobs_pat = re.compile(r'(?i)^jobs.*?:\s*(\d+)\s*$')
        ren_pat  = re.compile(r'(?i)-\s*renewable\s*:?\s*(\d+)\s*R')
        non_pat  = re.compile(r'(?i)-\s*nonrenewable\s*:?\s*(\d+)\s*N')

        # Header
        while idx < n:
            s = lines[idx].strip()
            if not s: idx += 1; continue
            m = jobs_pat.match(s)
            if m: data['num_jobs'] = int(m.group(1)); idx += 1; continue
            m = ren_pat.search(s)
            if m: data['num_renewable'] = int(m.group(1)); idx += 1; continue
            m = non_pat.search(s)
            if m: data['num_nonrenewable'] = int(m.group(1)); idx += 1; continue
            if re.match(r'(?i)^PRECEDENCE RELATIONS', s):
                idx += 1; break
            idx += 1

        # Precedence
        data['precedence'] = {}; data['num_modes'] = {}
        while idx < n and (not lines[idx].strip() or lines[idx].lower().startswith("jobnr.") or set(lines[idx].strip()) in ({'-'}, {'*'})):
            idx += 1

        while idx < n:
            s = lines[idx].strip()
            if re.match(r'(?i)^REQUESTS/DURATIONS:?$', s):
                idx += 1; break
            if not s or s.lower().startswith("jobnr.") or set(s) in ({'-'}, {'*'}):
                idx += 1; continue
            parts = s.split()
            if not parts[0].isdigit():
                idx += 1; continue
            j = int(parts[0])
            if len(parts) >= 2 and parts[1].isdigit():
                data['num_modes'][j] = int(parts[1])
            succs = [int(t) for t in parts[3:] if t.isdigit()]
            data['precedence'][j] = succs
            idx += 1

        # Requests/Durations
        R = data.get('num_renewable', 0); N = data.get('num_nonrenewable', 0)
        job_modes, cur = {}, None

        while idx < n and (
                not lines[idx].strip() or lines[idx].lower().startswith("jobnr.") or set(lines[idx].strip()) == {'-'}):
            idx += 1

        while idx < n:
            s = lines[idx].strip()
            # dừng khi tới RESOURCE AVAILABILITIES
            if re.match(r'^\*{5,}$', s) or re.match(r'(?i)^RESOURCE AVAILABILITIES', s):
                break
            if not s:
                idx += 1;
                continue

            parts = s.split()
            # --- phân biệt bằng số cột ---
            if parts[0].isdigit():
                if len(parts) >= 3 + R + N:
                    # DÒNG JOB MỚI: jobnr, mode, dur, R..., N...
                    cur = int(parts[0])
                    dur = int(parts[2])
                    reqs = [int(x) for x in parts[3:3 + R + N]]
                    job_modes.setdefault(cur, []).append((dur, reqs))
                elif len(parts) >= 2 + R + N and cur is not None:
                    # DÒNG MODE TIẾP THEO: mode, dur, R..., N...
                    dur = int(parts[1])
                    reqs = [int(x) for x in parts[2:2 + R + N]]
                    job_modes.setdefault(cur, []).append((dur, reqs))
                # nếu không đủ cột thì bỏ qua
            # dòng khác -> bỏ
            idx += 1

        data['job_modes'] = job_modes

        # Resource capacities
        while idx < n and not re.match(r'(?i)^RESOURCE AVAILABILITIES', lines[idx].strip()):
            idx += 1
        if idx < n and re.match(r'(?i)^RESOURCE AVAILABILITIES', lines[idx].strip()):
            idx += 1
            while idx < n and not re.match(r'^\s*\d', lines[idx].strip()):
                idx += 1
            caps = []
            if idx < n:
                caps = [int(t) for t in lines[idx].split() if t.isdigit()]
                idx += 1
            data['renewable_capacity'] = caps[:R] if R else []
            data['nonrenewable_capacity'] = caps[R:R+N] if N else []
        else:
            data['renewable_capacity'] = [0]*R
            data['nonrenewable_capacity'] = [0]*N

        # optional horizon
        for ln in lines:
            if ln.strip().lower().startswith("horizon"):
                toks = ln.strip().split()
                try: data['horizon'] = int(toks[-1])
                except: pass
                break

        return data

    def get_horizon(self):
        if 'horizon' in self.data:
            return self.data['horizon']
        total = 0
        for _, modes in self.data.get('job_modes', {}).items():
            if modes: total += max(m[0] for m in modes)
        return max(total, 1)
def _critical_path_lb_mmlib(reader: MMLIB50Reader):
    prec = reader.data.get('precedence', {})
    modes = reader.data.get('job_modes', {})
    memo = {}
    def f(j):
        if j in memo: return memo[j]
        succs = prec.get(j, [])
        succ_max = max((f(s) for s in succs), default=0)
        dur_min = min((m[0] for m in modes.get(j, [])), default=0)
        memo[j] = dur_min + succ_max
        return memo[j]
    return max(f(1), 1)

def run_one_mmlib50(instance_path: str, timeout_s: int = 600):
    """
    Giải duy nhất 1 instance MMLIB50 với chiến lược:
      - LB = max(CPM(d_min), Energetic LB)
      - UB = min(horizon, UB từ SSGS)
      - Duyệt giảm từ UB với bước thích ứng (halving) + quick filter energetic,
    """
    from time import time
    print("=" * 100)
    print("RUN ONE MMLIB50 INSTANCE")
    print("=" * 100)
    print(f"Instance: {instance_path}")

    reader = MMLIB50Reader(instance_path)
    enc = MRCPSPBlockBasedStaircase(reader)

    # --- LB/UB ---
    # Dữ liệu cho LB energetic lấy từ encoder (đã preprocess)
    data_for_lb = {
        'num_jobs': enc.jobs,
        'num_renewable': enc.renewable_resources,
        'num_nonrenewable': enc.nonrenewable_resources,
        'renewable_capacity': enc.R_capacity,
        'nonrenewable_capacity': enc.N_capacity,
        'precedence': enc.precedence,
        'job_modes': enc.job_modes,
    }
    lb_cpm    = enc.calculate_critical_path_bound()
    lb_energy = compute_lb_energetic(data_for_lb)
    lb        = max(lb_cpm, lb_energy)

    ub_ssgs = compute_ub_ssgs(reader, restarts=16, seed=4000)  # bạn có thể chỉnh 8–16
    ub      = min(reader.get_horizon(), ub_ssgs)
    if ub < lb:
        ub = lb

    # --- Solve theo chiến lược energetic (descend + adaptive step) ---
    t0 = time()
    best_ms, best_model = None, None

    # Thử UB trước (thường FEAS rất nhanh)
    if time() - t0 <= timeout_s:
        sol = enc.solve(ub)  # giữ nguyên solve() để in như cũ
        if sol:
            best_ms, best_model = ub, sol
            if ub == lb:
                dt = time() - t0
                print(f"\n✓ Found feasible/optimal makespan = {best_ms} (time {dt:.2f}s)")
                try:
                    enc.print_solution(best_model, best_ms)
                    enc.validate_solution(best_model)
                except Exception:
                    pass
                return

    # Giảm dần với bước thích ứng
    B    = best_ms if best_ms is not None else ub
    step = max(1, (ub - lb) // 4)

    while step >= 1:
        if time() - t0 > timeout_s:
            break

        cand = B - step
        if cand < lb:
            step //= 2
            continue

        # Quick filter energetic: dưới LB energetic thì bỏ qua, không encode
        if cand < lb_energy:
            lb = max(lb, cand + 1)
            step //= 2
            continue

        sol = enc.solve(cand)  # giữ nguyên solve() để in như cũ

        if time() - t0 > timeout_s:
            break

        if sol:
            B = cand
            best_ms, best_model = B, sol
            if B == lb:
                break
            # vẫn giữ step để đi nhanh khi còn xa LB
            continue
        else:
            # Gặp UNSAT thì thu hẹp bước
            step //= 2
            continue

    dt = time() - t0
    if best_ms is not None:
        print(f"\n✓ Found feasible/optimal makespan = {best_ms} (time {dt:.2f}s)")
        try:
            enc.print_solution(best_model, best_ms)
            enc.validate_solution(best_model)
        except Exception:
            pass
    else:
        print(f"\n✗ No solution within {timeout_s}s (lb={lb}, ub={ub})")

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

    def _add_pb_via_savilerow(
            self,
            pb_list: list[tuple[list[int], list[int], int]],
            batch_size: int = 1200,
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
                        ok = False;
                        break
                # non-renewables
                if ok:
                    for k in range(self.nonrenewable_resources):
                        idx = R + k
                        if idx < len(req) and req[idx] > self.N_capacity[k]:
                            ok = False;
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
                        dominated = True;
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
                        to_remove.add(w);
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
            u = q.popleft();
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
            u = q.popleft();
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
                    succ[i].add(j);
                    added += 1
                elif must_j_before_i and (pos.get(j, -1) < pos.get(i, 10 ** 9)):
                    succ[j].add(i);
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

    def create_blocks_for_precedence(self, pred_job, succ_job):
        """
        Create blocks for successor based on precedence relationship
        Each precedence pair gets its own block structure
        """

        current_variable = self.va
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

        # Also aggregate into job-level view
        if succ_job not in self.job_blocks:
            self.job_blocks[succ_job] = []
        self.job_blocks[succ_job].extend(blocks)

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

    def create_variables(self):
        """Create all variables"""
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

        # u_{j,t,m} process variables
        self.u_vars = {}
        for j in range(1, self.jobs + 1):
            self.u_vars[j] = {}
            for t in range(self.horizon + 1):
                self.u_vars[j][t] = {}
                for m in range(len(self.job_modes[j])):
                    duration = self.job_modes[j][m][0]
                    if t - duration + 1 <= self.LS[j] and t >= self.ES[j]:
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
        """Precedence using job-level SCAMO y-vars.
        For (pred->succ), if pred starts at t with mode m (dur=d), forbid succ start times ≤ t+d-1 by
        setting certain prefix y-vars (or first x) to 0 via conditional clauses.
        """
        current_variable = self.stats["variables"]
        current_clauses = self.stats["clauses"]

        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence:
                continue
            for succ in self.precedence[pred]:
                # ensure succ blocks exist and encoded
                if succ not in self.job_blocks or not self.job_blocks[succ]:
                    blocks = self.create_blocks_for_job(succ)
                    for (bid, st, en, _bt, _a, _b) in blocks:
                        self.encode_amo_block(bid, succ, st, en)
                    for i in range(len(blocks) - 1):
                        self.connect_blocks(blocks[i][0], blocks[i + 1][0])
                blocks = sorted(self.job_blocks[succ], key=lambda b: b[1])
                for m_pred, mode in enumerate(self.job_modes[pred]):
                    dur = mode[0]
                    for t_pred in range(self.ES[pred], self.LS[pred] + 1):
                        if t_pred not in self.s_vars[pred]:
                            continue
                        thr = t_pred + dur - 1
                        if thr < self.ES[succ]:
                            continue
                        # 1) For every block fully <= threshold: forbid entire block
                        for (bid, st, en, _bt, _a, _b) in blocks:
                            last_t = en - 1
                            if last_t <= thr and st <= last_t:
                                y, x = self.create_register_bits_for_block(bid, succ, st, en)
                                k = len(x)
                                if k == 1:
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[0]])
                                    self.stats['clauses'] += 1
                                elif k >= 2:
                                    self.cnf.append(
                                        [-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -y[k - 2]])
                                    self.cnf.append(
                                        [-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[k - 1]])
                                    self.stats['clauses'] += 2

                        # 2) For the block that contains threshold: forbid up to (thr)
                        for (bid, st, en, _bt, _a, _b) in blocks:
                            if st <= thr < en:
                                y, x = self.create_register_bits_for_block(bid, succ, st, en)
                                k = len(x)
                                idx = thr - st
                                if idx == 0:
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[0]])
                                    self.stats['clauses'] += 1
                                elif idx < k - 1:
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -y[idx]])
                                    self.stats['clauses'] += 1
                                else:  # idx == k-1
                                    if k == 1:
                                        self.cnf.append(
                                            [-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[0]])
                                        self.stats['clauses'] += 1
                                    else:
                                        self.cnf.append(
                                            [-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -y[k - 2]])
                                        self.cnf.append(
                                            [-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[k - 1]])
                                        self.stats['clauses'] += 2
                                break  # only one containing block

        staircase_variable = self.stats["variables"] - current_variable
        staircase_clauses =  self.stats["clauses"] - current_clauses

        print(f"Number of STAIRCASE variables: {staircase_variable}")
        print(f"Number of STAIRCASE clauses: {staircase_clauses}")

    def add_process_variable_constraints(self):
        """Define process variables"""
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
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
        """Encode with precedence-aware blocks"""
        print("\n=== ENCODING WITH PRECEDENCE-AWARE BLOCKS ===")

        print("Creating variables...")
        self.create_variables()

        print("Adding start time constraints...")
        self.add_start_time_constraints()

        print("Adding mode selection constraints...")
        self.add_mode_selection_constraints()

        print("Adding precedence constraints with adaptive blocks...")
        self.add_precedence_constraints_with_blocks()

        print("Adding process variable constraints...")
        self.add_process_variable_constraints()

        print("Adding renewable resource constraints...")
        self.add_renewable_resource_constraints()

        print("Adding non-renewable resource constraints...")
        self.add_nonrenewable_resource_constraints()

        if makespan is not None:
            print(f"Adding makespan constraint: {makespan}")
            self.add_makespan_constraint(makespan)

        self.stats['clauses'] = len(self.cnf.clauses)

        print(f"\n=== ENCODING STATISTICS ===")
        print(f"Total variables: {self.vpool.top if hasattr(self.vpool, 'top') else self.vpool._top}")
        print(f"  - Basic vars: {self.stats['variables']}")
        print(f"  - Register bits: {self.stats['register_bits']}")
        print(f"Total clauses: {self.stats['clauses']}")
        print(f"Connection clauses: {self.stats['connection_clauses']}")
        print(f"Precedence pairs encoded: {len(self.precedence_widths)}")

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

import subprocess, shutil, os, stat
from pathlib import Path

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


if __name__ == "__main__":
    DEFAULT_INSTANCE = "data/MMLIB50/J5013_5.mm"
    run_one_mmlib50(DEFAULT_INSTANCE, timeout_s=600)


