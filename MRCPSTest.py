"""
MRCPSP SAT-based Pseudo-Boolean Encoding sử dụng PySAT
Implement theo đúng công thức (6.1) - (6.17) trong tài liệu
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
from pysat.card import CardEnc, EncType


class MRCPSPDataReader:
    """Đọc dữ liệu MRCPSP từ file .mm"""

    def __init__(self, filename):
        self.filename = filename
        self.data = self.read_file()

    def read_file(self):
        """Đọc và parse file .mm"""
        with open(self.filename, 'r') as f:
            content = f.read()

        lines = [line.rstrip() for line in content.split('\n')]
        data = {}
        idx = 0

        # Skip header lines until we reach useful data
        while idx < len(lines):
            line = lines[idx].strip()
            if line.startswith("jobs (incl. supersource/sink"):
                parts = line.split()
                total_jobs = int(parts[-1])
                data['num_jobs'] = total_jobs
                break
            idx += 1

        # Find resource information
        while idx < len(lines):
            line = lines[idx].strip()
            if "- renewable" in line:
                parts = line.split()
                data['num_renewable'] = int(parts[3])
            elif "- nonrenewable" in line:
                parts = line.split()
                data['num_nonrenewable'] = int(parts[3])
            elif line.startswith("PRECEDENCE RELATIONS:"):
                idx += 1
                break
            idx += 1

        # Read precedence relations
        data['precedence'] = {}
        data['num_modes'] = {}

        while idx < len(lines):
            line = lines[idx].strip()
            if line.startswith("REQUESTS/DURATIONS:"):
                break
            if line and not line.startswith("jobnr."):
                parts = line.split()
                if len(parts) >= 3:
                    job_id = int(parts[0])
                    num_modes = int(parts[1])
                    num_successors = int(parts[2])

                    successors = []
                    for i in range(3, 3 + num_successors):
                        if i < len(parts):
                            successors.append(int(parts[i]))

                    data['precedence'][job_id] = successors
                    data['num_modes'][job_id] = num_modes
            idx += 1

        # Skip to job modes section
        while idx < len(lines):
            line = lines[idx].strip()
            if line.startswith("jobnr. mode duration"):
                idx += 2  # Skip header and separator line
                break
            idx += 1

        # Read job modes
        data['job_modes'] = {}
        for j in range(1, data['num_jobs'] + 1):
            data['job_modes'][j] = []

        current_job_id = None

        while idx < len(lines):
            line = lines[idx]
            stripped_line = line.strip()

            if stripped_line.startswith("RESOURCEAVAILABILITIES:"):
                break

            if not stripped_line or stripped_line.startswith("*") or stripped_line.startswith("-"):
                idx += 1
                continue

            parts = stripped_line.split()
            if len(parts) >= 6:
                try:
                    if len(parts) == 7:
                        # Job line
                        current_job_id = int(parts[0])
                        mode_id = int(parts[1])
                        duration = int(parts[2])
                        resources = [int(parts[3]), int(parts[4]), int(parts[5]), int(parts[6])]

                        if current_job_id <= data['num_jobs']:
                            data['job_modes'][current_job_id].append((duration, resources))

                    elif len(parts) == 6 and current_job_id is not None:
                        # Mode line
                        mode_id = int(parts[0])
                        duration = int(parts[1])
                        resources = [int(parts[2]), int(parts[3]), int(parts[4]), int(parts[5])]

                        if current_job_id <= data['num_jobs']:
                            data['job_modes'][current_job_id].append((duration, resources))

                except (ValueError, IndexError):
                    pass

            idx += 1

        # Read resource availabilities
        while idx < len(lines):
            line = lines[idx].strip()
            if line and not line.startswith("*") and not line.startswith("R "):
                parts = line.split()
                if len(parts) >= 4:
                    try:
                        data['renewable_capacity'] = [int(parts[0]), int(parts[1])]
                        data['nonrenewable_capacity'] = [int(parts[2]), int(parts[3])]
                        break
                    except ValueError:
                        pass
            idx += 1

        return data

    def get_horizon(self):
        """Tính horizon dựa trên tổng duration lớn nhất"""
        total_duration = 0
        for j in range(1, self.data['num_jobs'] + 1):
            if j in self.data['job_modes'] and self.data['job_modes'][j]:
                max_duration = max(mode[0] for mode in self.data['job_modes'][j])
                total_duration += max_duration
        return min(total_duration, 100)

"Encoder theo đúng công thức (6.1) - (6.17)"
class MRCPSPSATEncoder:

    def __init__(self, mm_reader):
        self.cnf = CNF()
        self.vpool = IDPool()  # Use IDPool instead of dict

        # Lấy dữ liệu
        self.jobs = mm_reader.data['num_jobs']
        self.horizon = mm_reader.get_horizon()
        self.renewable_resources = mm_reader.data['num_renewable']
        self.nonrenewable_resources = mm_reader.data['num_nonrenewable']

        self.R_capacity = mm_reader.data['renewable_capacity']
        self.N_capacity = mm_reader.data['nonrenewable_capacity']

        self.precedence = mm_reader.data['precedence']
        self.job_modes = mm_reader.data['job_modes']

        # Tính time windows cho mỗi job
        self.calculate_time_windows()

        print(f"Loaded: {self.jobs} jobs, horizon={self.horizon}")
        print(f"Renewable resources: {self.R_capacity}")
        print(f"Non-renewable resources: {self.N_capacity}")

    "Tạo biến mới với optional name"
    def get_new_var(self, name=None):
        if name:
            return self.vpool.id(name)
        else:
            return self.vpool._next()

    "Tính ES (earliest start) và LS (latest start) cho mỗi job"
    def calculate_time_windows(self):
        self.ES = {}
        self.LS = {}

        # Initialize
        for j in range(1, self.jobs + 1):
            self.ES[j] = 0
            self.LS[j] = self.horizon

        # Forward pass for ES
        self.ES[1] = 0  # Source starts at 0

        def calc_es(j):
            if j in self.ES and self.ES[j] > 0:
                return self.ES[j]

            max_pred_finish = 0
            # Tìm predecessors
            for pred in range(1, self.jobs + 1):
                if pred in self.precedence and j in self.precedence[pred]:
                    # pred -> j
                    pred_es = calc_es(pred)
                    min_duration = min(mode[0] for mode in self.job_modes[pred])
                    max_pred_finish = max(max_pred_finish, pred_es + min_duration)

            self.ES[j] = max_pred_finish
            return self.ES[j]

        for j in range(1, self.jobs + 1):
            calc_es(j)

        # Backward pass for LS (simplified - use horizon as upper bound)
        for j in range(1, self.jobs + 1):
            max_duration = max(mode[0] for mode in self.job_modes[j])
            self.LS[j] = self.horizon - max_duration

    "Tạo các biến theo công thức"
    def create_variables(self):

        # 1. S_i variables: thời điểm bắt đầu (sẽ encode bằng cách rời rạc hóa)
        # Dùng biến boolean s_{i,t} = 1 nếu S_i = t
        self.s_vars = {}
        for j in range(1, self.jobs + 1):
            self.s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = self.get_new_var(f's_{j}_{t}')
                self.s_vars[j][t] = var

        # 2. sm_{i,o} variables: chọn mode (công thức 6.10)
        self.sm_vars = {}
        for j in range(1, self.jobs + 1):
            self.sm_vars[j] = {}
            for m in range(len(self.job_modes[j])):
                var = self.get_new_var(f'sm_{j}_{m}')
                self.sm_vars[j][m] = var

        # 3. x_{i,t,o} variables: job i đang chạy tại thời điểm t với mode o (công thức 6.13)
        self.x_vars = {}
        for j in range(1, self.jobs + 1):
            self.x_vars[j] = {}
            for t in range(self.horizon + 1):
                self.x_vars[j][t] = {}
                for m in range(len(self.job_modes[j])):
                    var = self.get_new_var(f'x_{j}_{t}_{m}')
                    self.x_vars[j][t][m] = var

    "Ràng buộc: mỗi job có đúng một thời điểm bắt đầu"
    def add_start_time_constraints(self):
        for j in range(1, self.jobs + 1):
            # Exactly one start time
            lits = []
            for t in range(self.ES[j], self.LS[j] + 1):
                if t in self.s_vars[j]:
                    lits.append(self.s_vars[j][t])

            if lits:
                # At least one
                self.cnf.append(lits)

                # At most one
                for i in range(len(lits)):
                    for k in range(i + 1, len(lits)):
                        self.cnf.append([-lits[i], -lits[k]])

    "Ràng buộc chọn mode (công thức 6.11, 6.12, 6.17)"
    def add_mode_selection_constraints(self):
        for j in range(1, self.jobs + 1):
            mode_vars = []
            for m in range(len(self.job_modes[j])):
                mode_vars.append(self.sm_vars[j][m])

            # Exactly one mode (công thức 6.17)
            # At least one
            self.cnf.append(mode_vars)

            # At most one
            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    self.cnf.append([-mode_vars[i], -mode_vars[k]])

    "Ràng buộc precedence (công thức 6.2, 6.9)"
    def add_precedence_constraints(self):
        for j in range(1, self.jobs + 1):
            if j not in self.precedence:
                continue

            for successor in self.precedence[j]:
                # Với mỗi mode của j
                for m_j in range(len(self.job_modes[j])):
                    duration_j = self.job_modes[j][m_j][0]

                    # sm_{j,m_j} => S_successor >= S_j + duration_j
                    # Tức là: sm_{j,m_j} AND s_{j,t_j} => NOT s_{successor,t_s} for t_s < t_j + duration_j

                    for t_j in range(self.ES[j], self.LS[j] + 1):
                        if t_j not in self.s_vars[j]:
                            continue

                        completion_j = t_j + duration_j

                        for t_s in range(self.ES[successor], min(completion_j, self.LS[successor] + 1)):
                            if t_s in self.s_vars[successor]:
                                # NOT(sm_{j,m_j} AND s_{j,t_j} AND s_{successor,t_s})
                                self.cnf.append([
                                    -self.sm_vars[j][m_j],
                                    -self.s_vars[j][t_j],
                                    -self.s_vars[successor][t_s]
                                ])

    "Định nghĩa biến x_{i,t,o} (công thức 6.13)"
    def add_running_variable_constraints(self):
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
                for m in range(len(self.job_modes[j])):
                    duration = self.job_modes[j][m][0]

                    # x_{j,t,m} = 1 <=> sm_{j,m} = 1 AND S_j <= t < S_j + duration
                    # Tương đương: x_{j,t,m} = 1 <=> sm_{j,m} = 1 AND OR(s_{j,t'} for t' in valid range)

                    valid_starts = []
                    for t_start in range(max(self.ES[j], t - duration + 1), min(t + 1, self.LS[j] + 1)):
                        if t_start in self.s_vars[j] and t_start + duration > t:
                            valid_starts.append(self.s_vars[j][t_start])

                    if valid_starts:
                        # x_{j,t,m} => sm_{j,m}
                        self.cnf.append([-self.x_vars[j][t][m], self.sm_vars[j][m]])

                        # x_{j,t,m} => OR(valid_starts)
                        self.cnf.append([-self.x_vars[j][t][m]] + valid_starts)

                        # sm_{j,m} AND any valid_start => x_{j,t,m}
                        for start_var in valid_starts:
                            self.cnf.append([-self.sm_vars[j][m], -start_var, self.x_vars[j][t][m]])
                    else:
                        # No valid starts => x_{j,t,m} = 0
                        self.cnf.append([-self.x_vars[j][t][m]])

    "Ràng buộc renewable resources (công thức 6.14)"
    def add_renewable_resource_constraints(self):
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
                # Collect variables and weights for PB constraint
                resource_vars = []
                resource_weights = []

                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        if len(self.job_modes[j][m][1]) > k:
                            resource_req = self.job_modes[j][m][1][k]
                            if resource_req > 0:
                                resource_vars.append(self.x_vars[j][t][m])
                                resource_weights.append(resource_req)

                # PB constraint: sum <= capacity
                if resource_vars:
                    pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                                self.R_capacity[k], vpool=self.vpool)
                    self.cnf.extend(pb_constraint)

    "Ràng buộc non-renewable resources (công thức 6.15)"
    def add_nonrenewable_resource_constraints(self):
        for k in range(self.nonrenewable_resources):
            resource_vars = []
            resource_weights = []

            for j in range(1, self.jobs + 1):
                for m in range(len(self.job_modes[j])):
                    resource_idx = self.renewable_resources + k
                    if len(self.job_modes[j][m][1]) > resource_idx:
                        resource_req = self.job_modes[j][m][1][resource_idx]
                        if resource_req > 0:
                            # Use sm_{j,m} variable
                            resource_vars.append(self.sm_vars[j][m])
                            resource_weights.append(resource_req)

            # PB constraint: total usage <= capacity
            if resource_vars:
                pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                           self.N_capacity[k], vpool=self.vpool)
                self.cnf.extend(pb_constraint)

    "Ràng buộc makespan (công thức 6.1)"
    def add_makespan_constraint(self, makespan):
        # Job cuối (sink) phải bắt đầu <= makespan
        sink_job = self.jobs

        for t in range(makespan + 1, self.LS[sink_job] + 1):
            if t in self.s_vars[sink_job]:
                self.cnf.append([-self.s_vars[sink_job][t]])

    "Giải với makespan cho trước"
    def solve(self, makespan):
        print(f"\n--- Thử makespan = {makespan} ---")

        # Reset
        self.cnf = CNF()
        self.var_counter = 1
        self.variables = {}

        # Create all variables
        self.create_variables()

        # Add all constraints
        self.add_start_time_constraints()
        self.add_mode_selection_constraints()
        self.add_precedence_constraints()
        self.add_running_variable_constraints()
        self.add_renewable_resource_constraints()
        self.add_nonrenewable_resource_constraints()
        self.add_makespan_constraint(makespan)

        print(f"Tổng số biến: {self.var_counter - 1}")
        print(f"Tổng số clause: {len(self.cnf.clauses)}")

        # Solve
        solver = Glucose42()
        solver.append_formula(self.cnf)

        if solver.solve():
            return self.extract_solution(solver.get_model())
        else:
            return None

    def extract_solution(self, model):
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

    "Tìm makespan tối ưu"
    def find_optimal_makespan(self):
        # Calculate bounds
        min_makespan = self.calculate_critical_path_bound()
        max_makespan = self.horizon

        best_makespan = None
        best_solution = None

        print(f"Tìm makespan tối ưu trong [{min_makespan}, {max_makespan}]")

        # Binary search
        while min_makespan <= max_makespan:
            mid = (min_makespan + max_makespan) // 2

            solution = self.solve(mid)

            if solution:
                best_makespan = mid
                best_solution = solution
                max_makespan = mid - 1
            else:
                min_makespan = mid + 1

        return best_makespan, best_solution

    "Tính critical path lower bound"
    def calculate_critical_path_bound(self):
        # Use ES calculation
        return self.ES[self.jobs] if self.jobs in self.ES else 1

    def validate_solution(self, solution):
        print("\n--- KIỂM TRA LỜI GIẢI ---")
        valid = True

        # Check precedence
        print("Kiểm tra precedence...")
        for j in range(1, self.jobs + 1):
            if j in solution and j in self.precedence:
                for succ in self.precedence[j]:
                    if succ in solution:
                        if solution[j]['finish_time'] > solution[succ]['start_time']:
                            print(f"Vi phạm precedence: {j} -> {succ}")
                            valid = False

        # Check renewable resources
        print("Kiểm tra renewable resources...")
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
                usage = 0
                for j in solution:
                    if solution[j]['start_time'] <= t < solution[j]['finish_time']:
                        usage += solution[j]['resources'][k]

                if usage > self.R_capacity[k]:
                    print(f"Vi phạm renewable resource {k+1} tại t={t}: {usage} > {self.R_capacity[k]}")
                    valid = False

        # Check non-renewable resources
        print("Kiểm tra non-renewable resources...")
        for k in range(self.nonrenewable_resources):
            total_usage = 0
            for j in solution:
                total_usage += solution[j]['resources'][self.renewable_resources + k]

            if total_usage > self.N_capacity[k]:
                print(f"Vi phạm non-renewable resource {k+1}: {total_usage} > {self.N_capacity[k]}")
                valid = False

        if valid:
            print("Lời giải hợp lệ!")

        return valid

    def print_solution(self, solution, makespan):
        print(f"\n=== LỜI GIẢI TỐI ƯU ===")
        print(f"Makespan: {makespan}")
        print("\nLịch trình:")
        print("Job | Mode | Start | Duration | Finish | Resources")
        print("-" * 60)

        for j in sorted(solution.keys()):
            info = solution[j]
            res_str = ' '.join(f"{r:2d}" for r in info['resources'])
            print(f"{j:3d} | {info['mode']+1:4d} | {info['start_time']:5d} | "
                  f"{info['duration']:8d} | {info['finish_time']:6d} | {res_str}")


def main():
    filename = "data/j102_5.mm"

    print(f"Đọc dữ liệu từ file: {filename}")

    try:
        # Read data
        reader = MRCPSPDataReader(filename)

        # Create encoder
        encoder = MRCPSPSATEncoder(reader)

        # Find optimal makespan
        optimal_makespan, solution = encoder.find_optimal_makespan()

        if optimal_makespan and solution:
            encoder.print_solution(solution, optimal_makespan)
            encoder.validate_solution(solution)
        else:
            print("Không tìm thấy lời giải!")

    except FileNotFoundError:
        print(f"Lỗi: Không tìm thấy file '{filename}'")
    except Exception as e:
        print(f"Lỗi: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()