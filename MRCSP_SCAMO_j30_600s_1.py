"""
MRCPSP Block-Based Staircase Encoding với Precedence-Aware Adaptive Width
Batch runner: quét toàn bộ .mm trong data/j10, giải với timeout 600s/instance,
ghi CSV định kỳ 10 dòng/lần vào result/j10/ và (nếu cấu hình) upload lên GCS.
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
import time
import math
from pathlib import Path
import csv
from datetime import datetime

# GCS (tùy chọn)
try:
    from google.cloud import storage  # pip install google-cloud-storage
    _GCS_AVAILABLE = True
except Exception:
    storage = None
    _GCS_AVAILABLE = False

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
        self.calculate_time_windows()

        # Precedence-aware block widths
        self.precedence_widths = {}  # {(pred, succ): width}
        self.calculate_precedence_widths()

        # Block structures
        self.precedence_blocks = {}
        self.job_blocks = {}
        self.register_bits = {}
        self.block_connections = []

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

    def calculate_time_windows(self):
        """Calculate ES và LS cho từng job"""
        self.ES = {}
        self.LS = {}

        for j in range(1, self.jobs + 1):
            self.ES[j] = 0
            self.LS[j] = self.horizon

        processed = set()

        def calc_es(j):
            if j in processed:
                return self.ES[j]

            max_pred_finish = 0
            for pred in range(1, self.jobs + 1):
                if pred in self.precedence and j in self.precedence[pred]:
                    pred_es = calc_es(pred)
                    if pred in self.job_modes and self.job_modes[pred]:
                        min_duration = min(mode[0] for mode in self.job_modes[pred])
                        max_pred_finish = max(max_pred_finish, pred_es + min_duration)

            self.ES[j] = max_pred_finish
            processed.add(j)
            return self.ES[j]

        for j in range(1, self.jobs + 1):
            calc_es(j)

        # Backward pass for LS
        for j in range(1, self.jobs + 1):
            if j in self.job_modes and self.job_modes[j]:
                max_duration = max(mode[0] for mode in self.job_modes[j])
                self.LS[j] = min(self.LS[j], self.horizon - max_duration)

    def get_adaptive_width_for_precedence(self, pred_job, succ_job):
        pred_durations = [mode[0] for mode in self.job_modes[pred_job]]
        pred_min_duration = min(pred_durations)
        pred_max_duration = max(pred_durations)

        earliest_succ = self.ES[pred_job] + pred_min_duration
        latest_succ = self.LS[pred_job] + pred_max_duration

        constrained_start = max(self.ES[succ_job], earliest_succ)
        constrained_end = min(self.LS[succ_job], latest_succ)
        effective_window = max(0, constrained_end - constrained_start + 1)

        duration_variability = pred_max_duration - pred_min_duration
        pred_modes = len(self.job_modes[pred_job])
        succ_modes = len(self.job_modes[succ_job])
        mode_combinations = pred_modes * succ_modes

        if effective_window <= 0:
            base_width = 10
        elif effective_window <= 5:
            base_width = 3
        elif effective_window <= 15:
            base_width = 4
        elif effective_window <= 30:
            base_width = int(math.sqrt(effective_window))
        else:
            base_width = min(12, int(effective_window / 6))

        if duration_variability >= 5:
            base_width = max(3, base_width - 2)
        elif duration_variability == 0:
            base_width = min(15, base_width + 2)

        if mode_combinations > 9:
            base_width = max(3, base_width - 1)

        return max(3, min(base_width, 15))

    def calculate_precedence_widths(self):
        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence:
                continue
            for succ in self.precedence[pred]:
                width = self.get_adaptive_width_for_precedence(pred, succ)
                self.precedence_widths[(pred, succ)] = width

    def create_blocks_for_job(self, job, width=None):
        es, ls = self.ES[job], self.LS[job]
        if width is None:
            win = max(1, ls - es + 1)
            width = max(6, int(math.sqrt(win)))
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
        self.job_blocks[job] = blocks
        return blocks

    def create_register_bits_for_block(self, block_id, job, start, end):
        if block_id in self.register_bits:
            return self.register_bits[block_id]
        x_vars, y_vars = [], []
        for t in range(start, end):
            # x là biến start-time
            if t in self.s_vars[job]:
                x_vars.append(self.s_vars[job][t])
        if len(x_vars) >= 2:
            for j in range(1, len(x_vars)):
                y = self.vpool.id(f'R_{block_id}_{j}')
                y_vars.append(y)
                self.stats['register_bits'] += 1
        self.register_bits[block_id] = (y_vars, x_vars)
        return y_vars, x_vars

    def encode_amo_block(self, block_id, job, start, end):
        if block_id in self.encoded_blocks:
            return
        y_vars, x_vars = self.create_register_bits_for_block(block_id, job, start, end)
        k = len(x_vars)
        if k <= 1:
            self.encoded_blocks.add(block_id)
            return
        self.cnf.append([-x_vars[0], y_vars[0]])
        self.stats['clauses'] += 1
        for j in range(1, k-1):
            self.cnf.append([-x_vars[j], y_vars[j]])
            self.stats['clauses'] += 1
        for j in range(0, k-2):
            self.cnf.append([-y_vars[j], y_vars[j+1]])
            self.stats['clauses'] += 1
        for j in range(1, k):
            self.cnf.append([-x_vars[j], -y_vars[j-1]])
            self.stats['clauses'] += 1

    def connect_blocks(self, block1_id, block2_id):
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
        if y1 and y2:
            self.cnf.append([-y1[-1], y2[0]])
            self.stats['connection_clauses'] += 1
        if y1:
            self.cnf.append([-x2[0], -y1[-1]])
            self.stats['connection_clauses'] += 1

    def create_variables(self):
        self.s_vars = {}
        for j in range(1, self.jobs + 1):
            self.s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = self.vpool.id(f's_{j}_{t}')
                self.s_vars[j][t] = var
                self.stats['variables'] += 1

        self.sm_vars = {}
        for j in range(1, self.jobs + 1):
            self.sm_vars[j] = {}
            for m in range(len(self.job_modes[j])):
                var = self.vpool.id(f'sm_{j}_{m}')
                self.sm_vars[j][m] = var
                self.stats['variables'] += 1

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

    def add_start_time_constraints(self):
        for j in range(1, self.jobs + 1):
            vars_list = [self.s_vars[j][t] for t in range(self.ES[j], self.LS[j] + 1) if t in self.s_vars[j]]
            if vars_list:
                self.cnf.append(vars_list)
                self.stats['clauses'] += 1
            blocks = self.create_blocks_for_job(j)
            for (block_id, start, end, _bt, _a, _b) in blocks:
                self.encode_amo_block(block_id, j, start, end)
            for i in range(len(blocks) - 1):
                self.connect_blocks(blocks[i][0], blocks[i + 1][0])

    def add_mode_selection_constraints(self):
        for j in range(1, self.jobs + 1):
            mode_vars = [self.sm_vars[j][m] for m in range(len(self.job_modes[j]))]
            self.cnf.append(mode_vars)
            self.stats['clauses'] += 1
            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    self.cnf.append([-mode_vars[i], -mode_vars[k]])
                    self.stats['clauses'] += 1

    def add_precedence_constraints_with_blocks(self):
        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence:
                continue
            for succ in self.precedence[pred]:
                if succ not in self.job_blocks or not self.job_blocks[succ]:
                    blocks = self.create_blocks_for_job(succ)
                    for (bid, st, en, _bt, _a, _b) in blocks:
                        self.encode_amo_block(bid, succ, st, en)
                    for i in range(len(blocks)-1):
                        self.connect_blocks(blocks[i][0], blocks[i+1][0])
                blocks = sorted(self.job_blocks[succ], key=lambda b: b[1])
                for m_pred, mode in enumerate(self.job_modes[pred]):
                    dur = mode[0]
                    for t_pred in range(self.ES[pred], self.LS[pred]+1):
                        if t_pred not in self.s_vars[pred]:
                            continue
                        thr = t_pred + dur - 1
                        if thr < self.ES[succ]:
                            continue
                        for (bid, st, en, _bt, _a, _b) in blocks:
                            last_t = en - 1
                            if last_t <= thr and st <= last_t:
                                y, x = self.create_register_bits_for_block(bid, succ, st, en)
                                k = len(x)
                                if k == 1:
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[0]])
                                    self.stats['clauses'] += 1
                                elif k >= 2:
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -y[k - 2]])
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[k - 1]])
                                    self.stats['clauses'] += 2
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
                                else:
                                    if k == 1:
                                        self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[0]])
                                        self.stats['clauses'] += 1
                                    else:
                                        self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -y[k - 2]])
                                        self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -x[k - 1]])
                                        self.stats['clauses'] += 2
                                break

    def add_process_variable_constraints(self):
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
                        self.cnf.append([-self.u_vars[j][t][m], self.sm_vars[j][m]])
                        self.stats['clauses'] += 1
                        self.cnf.append([-self.u_vars[j][t][m]] + valid_starts)
                        self.stats['clauses'] += 1
                        for start_var in valid_starts:
                            self.cnf.append([-self.sm_vars[j][m], -start_var, self.u_vars[j][t][m]])
                            self.stats['clauses'] += 1
                    else:
                        self.cnf.append([-self.u_vars[j][t][m]])
                        self.stats['clauses'] += 1

    def add_renewable_resource_constraints(self):
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
                resource_vars, resource_weights = [], []
                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        if m in self.u_vars[j][t]:
                            if len(self.job_modes[j][m][1]) > k:
                                req = self.job_modes[j][m][1][k]
                                if req > 0:
                                    resource_vars.append(self.u_vars[j][t][m])
                                    resource_weights.append(req)
                if resource_vars:
                    pb = PBEnc.atmost(resource_vars, resource_weights, self.R_capacity[k], vpool=self.vpool)
                    self.cnf.extend(pb)

    def add_nonrenewable_resource_constraints(self):
        """
        Non-renewable with EO-reduction (4.4.1/3.2.5) + fallback:
          - m_i = min_o b_{iok}
          - B'_k = B_k - sum_i m_i
          - sum delta_{iok} * sm_{io} <= B'_k, where delta = max(0, b_{iok} - m_i)
          - if B'_k < 0  -> fallback to plain PB: sum b_{iok} * sm_{io} <= B_k
        """
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
                # Fallback an toàn: dùng PB gốc để tránh UNSAT giả
                resource_vars, resource_weights = _plain_pb_lists()
                if resource_vars:
                    pb = PBEnc.atmost(lits=resource_vars,
                                      weights=resource_weights,
                                      bound=Bk,
                                      vpool=self.vpool)
                    self.cnf.extend(pb)
            else:
                # EO-reduction chuẩn
                resource_vars, resource_weights = _eo_pb_lists()
                if resource_vars:
                    pb = PBEnc.atmost(lits=resource_vars,
                                      weights=resource_weights,
                                      bound=Bk_reduced,
                                      vpool=self.vpool)
                    self.cnf.extend(pb)

    def add_makespan_constraint(self, makespan):
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
        self.stats['clauses'] = len(self.cnf.clauses)
        self.last_clause_count = self.stats['clauses']
        self.last_var_count = self.vpool.top if hasattr(self.vpool, 'top') else getattr(self.vpool, '_top', 0)
        return self.cnf

    def solve(self, makespan):
        """Giải với makespan cho trước. Lưu solve_time vào self.last_solve_time."""
        # Reset cho mỗi lần mã hoá
        self.cnf = CNF()
        self.vpool = IDPool()
        self.precedence_blocks = {}
        self.job_blocks = {}
        self.register_bits = {}
        self.block_connections = []
        self.stats = {'variables': 0, 'clauses': 0, 'register_bits': 0, 'connection_clauses': 0}

        # Encode
        self.encode(makespan)

        solver = Glucose42()
        solver.append_formula(self.cnf)

        start_time = time.time()
        result = solver.solve()
        self.last_solve_time = time.time() - start_time

        if result:
            return self.extract_solution(solver.get_model())
        else:
            return None

    def extract_solution(self, model):
        solution = {}
        for j in range(1, self.jobs + 1):
            start_time_j = None
            for t in range(self.ES[j], self.LS[j] + 1):
                if t in self.s_vars[j] and self.s_vars[j][t] <= len(model) and model[self.s_vars[j][t] - 1] > 0:
                    start_time_j = t
                    break
            mode = None
            for m in range(len(self.job_modes[j])):
                if self.sm_vars[j][m] <= len(model) and model[self.sm_vars[j][m] - 1] > 0:
                    mode = m
                    break
            if start_time_j is not None and mode is not None:
                duration = self.job_modes[j][mode][0]
                resources = self.job_modes[j][mode][1]
                solution[j] = {
                    'mode': mode,
                    'start_time': start_time_j,
                    'duration': duration,
                    'finish_time': start_time_j + duration,
                    'resources': resources
                }
        return solution

    def calculate_critical_path_bound(self):
        """Lower bound theo critical path đơn giản"""
        critical_length = {}
        def get_critical_length(j):
            if j in critical_length:
                return critical_length[j]
            if j not in self.precedence or not self.precedence[j]:
                critical_length[j] = min((mode[0] for mode in self.job_modes.get(j, [])), default=0)
                return critical_length[j]
            max_path = 0
            for succ in self.precedence[j]:
                max_path = max(max_path, get_critical_length(succ))
            dur = min((mode[0] for mode in self.job_modes.get(j, [])), default=0)
            critical_length[j] = dur + max_path
            return critical_length[j]
        critical_path = get_critical_length(1)
        return max(critical_path, self.ES.get(self.jobs, 1))

# ==========================
#  Hàm tiện ích đọc .mm
# ==========================
def load_reader(mm_path):
    """Tải MRCPSPDataReader từ file .mm."""
    try:
        from MRCPSP_Basic import MRCPSPDataReader
    except Exception as e:
        raise ImportError(f"Không import được MRCPSPDataReader: {e}")
    return MRCPSPDataReader(str(mm_path))

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
#  Giải 1 instance với timeout & nhị phân makespan
# ==========================
def solve_instance_with_timeout(mm_path, timeout_s=600):
    """
    Trả về dict:
      instance, horizon, variables, clauses, makespan, status, solve_time, timeout
    - status: Optimal / Feasible / Infeasible
    - timeout: Yes/No
    """
    reader = load_reader(mm_path)
    enc = MRCPSPBlockBasedStaircase(reader)

    lb = enc.calculate_critical_path_bound()
    ub = reader.get_horizon()

    start = time.time()
    timeout_flag = False
    best_makespan = None
    best_vars = 0
    best_clauses = 0

    lo, hi = lb, ub
    while lo <= hi:
        now = time.time()
        if now - start > timeout_s:
            timeout_flag = True
            break

        mid = (lo + hi) // 2
        solution = enc.solve(mid)
        if time.time() - start > timeout_s:
            timeout_flag = True

        if solution:
            best_makespan = mid
            best_vars = enc.last_var_count
            best_clauses = enc.last_clause_count
            hi = mid - 1
        else:
            lo = mid + 1

        if timeout_flag:
            break

    total_time = time.time() - start

    if not timeout_flag:
        status = "Optimal" if best_makespan is not None else "Infeasible"
    else:
        status = "Feasible" if best_makespan is not None else "Infeasible"

    row = {
        "instance": Path(mm_path).name,
        "horizon": ub,
        "variables": best_vars if best_makespan is not None else enc.last_var_count,
        "clauses": best_clauses if best_makespan is not None else enc.last_clause_count,
        "makespan": best_makespan if best_makespan is not None else "",
        "status": status,
        "Solve time": f"{total_time:.2f}",
        "timeout": "Yes" if timeout_flag else "No",
    }
    return row

# ==========================
#  Chạy hàng loạt & ghi CSV theo lô 10 + upload GCS
# ==========================
def run_batch_j10(
    data_dir="data/j10",
    out_dir="result/j10",
    timeout_s=600,
    gcs_bucket: str | None = None,
    gcs_prefix: str | None = "result/j10"
):
    """
    Nếu gcs_bucket != None, mỗi lần ghi CSV sẽ upload file lên:
    gs://<gcs_bucket>/<gcs_prefix>/<csv_filename>
    """
    data_path = Path(data_dir)
    out_path = Path(out_dir)
    out_path.mkdir(parents=True, exist_ok=True)

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    csv_file = out_path / f"MRCPSP_j10_results_{ts}.csv"

    fields = ["instance", "horizon", "variables", "clauses",
              "makespan", "status", "Solve time", "timeout"]

    results = []
    mm_files = sorted(data_path.glob("*.mm"))
    print(f"Found {len(mm_files)} instances in {data_path}")

    # Ghi header ngay khi tạo file
    with csv_file.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()

    # Upload ngay sau khi tạo header (để có file rỗng trên GCS)
    if gcs_bucket:
        dest_blob = f"{gcs_prefix.rstrip('/')}/{csv_file.name}" if gcs_prefix else csv_file.name
        try:
            _upload_to_gcs(gcs_bucket, csv_file, dest_blob)
        except Exception as e:
            print(f"  ⚠ Không thể upload header lên GCS: {e}")

    for idx, mm in enumerate(mm_files, start=1):
        print(f"[{idx}/{len(mm_files)}] Solving {mm.name} ...")
        try:
            row = solve_instance_with_timeout(mm, timeout_s=timeout_s)
        except Exception as e:
            row = {
                "instance": mm.name,
                "horizon": "",
                "variables": "",
                "clauses": "",
                "makespan": "",
                "status": "Infeasible",
                "Solve time": "",
                "timeout": "No"
            }
            print(f"  -> Lỗi instance {mm.name}: {e}")

        results.append(row)

        # Ghi theo lô mỗi 10 dòng
        if idx % 10 == 0:
            with csv_file.open("a", newline="", encoding="utf-8") as f:
                writer = csv.DictWriter(f, fieldnames=fields)
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
            writer = csv.DictWriter(f, fieldnames=fields)
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
    # GỌI BATCH: thay "your-bucket-name" bằng bucket của bạn
    run_batch_j10(
        data_dir="data/j10",
        out_dir="result/j10",
        timeout_s=600,
        gcs_bucket="mrcpsp",
        gcs_prefix="result/j10"
    )
