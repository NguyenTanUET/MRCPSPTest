"""
MRCPSP SAT-based Pseudo-Boolean Encoding sử dụng PySAT
Implement theo đúng công thức (6.1) - (6.17) trong tài liệu
"""

import os
import csv
import time
import glob
from google.cloud import storage
from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose3
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


class MRCPSPSATEncoder:
    """Encoder theo đúng công thức (6.1) - (6.17)"""

    def __init__(self, mm_reader, timeout=600):
        self.cnf = CNF()
        self.vpool = IDPool()
        self.timeout = timeout

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

    def get_new_var(self, name=None):
        """Tạo biến mới với optional name"""
        if name:
            return self.vpool.id(name)
        else:
            return self.vpool._next()

    def calculate_time_windows(self):
        """Tính ES (earliest start) và LS (latest start) cho mỗi job"""
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

    def create_variables(self):
        """Tạo các biến theo công thức"""
        # 1. S_i variables: thời điểm bắt đầu (sẽ encode bằng cách rời rạc hóa)
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

    def add_start_time_constraints(self):
        """Ràng buộc: mỗi job có đúng một thời điểm bắt đầu"""
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

    def add_mode_selection_constraints(self):
        """Ràng buộc chọn mode (công thức 6.11, 6.12, 6.17)"""
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

    def add_precedence_constraints(self):
        """Ràng buộc precedence (công thức 6.2, 6.9)"""
        for j in range(1, self.jobs + 1):
            if j not in self.precedence:
                continue

            for successor in self.precedence[j]:
                # Với mỗi mode của j
                for m_j in range(len(self.job_modes[j])):
                    duration_j = self.job_modes[j][m_j][0]

                    for t_j in range(self.ES[j], self.LS[j] + 1):
                        if t_j not in self.s_vars[j]:
                            continue

                        completion_j = t_j + duration_j

                        for t_s in range(self.ES[successor], min(completion_j, self.LS[successor] + 1)):
                            if t_s in self.s_vars[successor]:
                                self.cnf.append([
                                    -self.sm_vars[j][m_j],
                                    -self.s_vars[j][t_j],
                                    -self.s_vars[successor][t_s]
                                ])

    def add_running_variable_constraints(self):
        """Định nghĩa biến x_{i,t,o} (công thức 6.13)"""
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
                for m in range(len(self.job_modes[j])):
                    duration = self.job_modes[j][m][0]

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

    def add_renewable_resource_constraints(self):
        """Ràng buộc renewable resources (công thức 6.14)"""
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
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

    def add_nonrenewable_resource_constraints(self):
        """Ràng buộc non-renewable resources (công thức 6.15)"""
        for k in range(self.nonrenewable_resources):
            resource_vars = []
            resource_weights = []

            for j in range(1, self.jobs + 1):
                for m in range(len(self.job_modes[j])):
                    resource_idx = self.renewable_resources + k
                    if len(self.job_modes[j][m][1]) > resource_idx:
                        resource_req = self.job_modes[j][m][1][resource_idx]
                        if resource_req > 0:
                            resource_vars.append(self.sm_vars[j][m])
                            resource_weights.append(resource_req)

            # PB constraint: total usage <= capacity
            if resource_vars:
                pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                             self.N_capacity[k], vpool=self.vpool)
                self.cnf.extend(pb_constraint)

    def add_makespan_constraint(self, makespan):
        """Ràng buộc makespan (công thức 6.1)"""
        sink_job = self.jobs

        for t in range(makespan + 1, self.LS[sink_job] + 1):
            if t in self.s_vars[sink_job]:
                self.cnf.append([-self.s_vars[sink_job][t]])

    def solve(self, makespan):
        """Giải với makespan cho trước"""
        start_time = time.time()

        # Reset
        self.cnf = CNF()

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

        # Solve with timeout
        solver = Glucose3()
        solver.append_formula(self.cnf)

        # Check if we're running out of time
        elapsed = time.time() - start_time
        if elapsed >= self.timeout:
            return None, True  # timeout

        # Set remaining time for solver
        remaining_time = max(1, int(self.timeout - elapsed))

        try:
            if solver.solve():
                return self.extract_solution(solver.get_model()), False
            else:
                return None, False
        except:
            return None, True  # timeout or error

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

    def find_optimal_makespan(self):
        """Tìm makespan tối ưu"""
        start_total_time = time.time()

        # Calculate bounds
        min_makespan = self.calculate_critical_path_bound()
        max_makespan = self.horizon

        best_makespan = None
        best_solution = None
        is_optimal = False
        status = "Infeasible"

        # Binary search
        while min_makespan <= max_makespan:
            # Check timeout
            if time.time() - start_total_time >= self.timeout:
                status = "Timeout"
                break

            mid = (min_makespan + max_makespan) // 2

            # Update remaining timeout for this solve attempt
            remaining_time = self.timeout - (time.time() - start_total_time)
            if remaining_time <= 0:
                status = "Timeout"
                break

            self.timeout = max(1, remaining_time)
            solution, timeout_occurred = self.solve(mid)

            if timeout_occurred:
                status = "Timeout"
                break

            if solution:
                best_makespan = mid
                best_solution = solution
                max_makespan = mid - 1
                status = "Feasible"
                # Check if this is optimal (no better solution possible)
                if mid == min_makespan:
                    is_optimal = True
                    status = "Optimal"
            else:
                min_makespan = mid + 1

        if is_optimal:
            status = "Optimal"
        elif best_makespan is not None:
            status = "Feasible"

        total_time = time.time() - start_total_time
        return best_makespan, best_solution, status, total_time

    def calculate_critical_path_bound(self):
        """Tính critical path lower bound"""
        return self.ES[self.jobs] if self.jobs in self.ES else 1


def upload_to_gcs(local_file_path, bucket_name, destination_path=None):
    """Upload file to Google Cloud Storage using google-cloud-storage library"""
    try:
        # Initialize client
        client = storage.Client()

        # Get bucket
        bucket = client.bucket(bucket_name)

        if destination_path is None:
            destination_path = os.path.basename(local_file_path)

        # Add timestamp to filename
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        name, ext = os.path.splitext(destination_path)
        destination_path = f"{name}_{timestamp}{ext}"

        # Upload file
        blob = bucket.blob(destination_path)

        print(f"Uploading {local_file_path} to gs://{bucket_name}/{destination_path}")

        # Upload with progress
        with open(local_file_path, 'rb') as file_obj:
            blob.upload_from_file(file_obj)

        print(f"File uploaded successfully to gs://{bucket_name}/{destination_path}")
        return True, f"gs://{bucket_name}/{destination_path}"

    except Exception as e:
        print(f"Error uploading to GCS: {e}")
        print("Possible solutions:")
        print("1. Set GOOGLE_APPLICATION_CREDENTIALS environment variable")
        print("2. Run 'gcloud auth application-default login'")
        print("3. Make sure the bucket exists and you have write permissions")
        return False, None


def get_j30_files(max_files=300):
    """Lấy danh sách 300 file đầu tiên từ thư mục data/j30"""
    j30_pattern = "data/j30/*.mm"
    all_files = glob.glob(j30_pattern)

    # Sort để đảm bảo thứ tự nhất quán
    all_files.sort()

    # Lấy 300 file đầu tiên
    return all_files[:max_files]


def solve_instance(instance_file, timeout=600):
    """Giải một instance và trả về kết quả"""
    try:
        # Extract instance name from file path
        instance_name = os.path.basename(instance_file).replace('.mm', '')

        # Read data
        reader = MRCPSPDataReader(instance_file)
        horizon = reader.get_horizon()

        # Create encoder with timeout
        encoder = MRCPSPSATEncoder(reader, timeout)

        # Find optimal makespan
        makespan, solution, status, solve_time = encoder.find_optimal_makespan()

        return {
            'instance': instance_name,
            'horizon': horizon,
            'makespan': makespan if makespan is not None else 'N/A',
            'status': status,
            'time': round(solve_time, 2)
        }

    except Exception as e:
        print(f"Error solving {instance_file}: {e}")
        return {
            'instance': os.path.basename(instance_file).replace('.mm', ''),
            'horizon': 'N/A',
            'makespan': 'N/A',
            'status': 'Error',
            'time': 'N/A'
        }


def main():
    # Configuration
    BUCKET_NAME = "mrcpsp"
    TIMEOUT_PER_INSTANCE = 600  # 10 phút cho mỗi instance

    # Ensure result directory exists
    os.makedirs('result', exist_ok=True)

    # Output CSV file với timestamp
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    output_file = f'result/MRCPSP_J30_300instances_{timestamp}.csv'

    # Get 300 files from j30 directory
    print("Đang tìm file trong thư mục data/j30...")
    instance_files = get_j30_files(max_files=300)

    print(f"Tìm thấy {len(instance_files)} file để chạy")
    print(f"Timeout cho mỗi instance: {TIMEOUT_PER_INSTANCE} giây")
    print(f"Tổng thời gian dự kiến tối đa: {len(instance_files) * TIMEOUT_PER_INSTANCE / 3600:.1f} giờ")

    if len(instance_files) == 0:
        print("Không tìm thấy file nào trong data/j30!")
        return

    # Results list
    results = []
    start_total_time = time.time()

    # Solve each instance
    for i, instance_file in enumerate(instance_files, 1):
        if os.path.exists(instance_file):
            print(f"\n[{i}/{len(instance_files)}] Solving {instance_file}...")

            # Calculate elapsed time
            elapsed_time = time.time() - start_total_time
            avg_time_per_instance = elapsed_time / i if i > 1 else 0
            estimated_remaining = (len(instance_files) - i) * avg_time_per_instance

            print(f"Elapsed: {elapsed_time / 3600:.1f}h, ETA: {estimated_remaining / 3600:.1f}h")

            result = solve_instance(instance_file, timeout=TIMEOUT_PER_INSTANCE)
            results.append(result)

            print(f"Result: {result['status']}, Makespan: {result['makespan']}, Time: {result['time']}s")

            # Save intermediate results every 10 instances
            if i % 10 == 0:
                print(f"Saving intermediate results... ({i} instances completed)")
                save_results_to_csv(results, output_file)

                # Try to upload intermediate results
                print("Uploading intermediate results to GCS...")
                success, gcs_path = upload_to_gcs(output_file, BUCKET_NAME)
                if success:
                    print(f"Intermediate results uploaded to {gcs_path}")

        else:
            print(f"File not found: {instance_file}")
            results.append({
                'instance': os.path.basename(instance_file).replace('.mm', ''),
                'horizon': 'N/A',
                'makespan': 'N/A',
                'status': 'File Not Found',
                'time': 'N/A'
            })

    # Save final results
    save_results_to_csv(results, output_file)

    total_time = time.time() - start_total_time
    print(f"\nHoàn thành! Tổng thời gian: {total_time / 3600:.2f} giờ")
    print(f"Results saved to: {output_file}")

    # Upload final results to Google Cloud Storage
    print(f"\nUploading final results to GCS bucket: {BUCKET_NAME}")
    success, gcs_path = upload_to_gcs(output_file, BUCKET_NAME)

    if success:
        print(f"Successfully uploaded final results to {gcs_path}")
    else:
        print("Failed to upload final results to GCS")

    # Display summary statistics
    display_summary(results)


def save_results_to_csv(results, output_file):
    """Lưu kết quả vào file CSV"""
    with open(output_file, 'w', newline='', encoding='utf-8') as csvfile:
        fieldnames = ['instance', 'horizon', 'makespan', 'status', 'time']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

        # Write header
        writer.writeheader()

        # Write results
        for result in results:
            writer.writerow(result)


def display_summary(results):
    """Hiển thị thống kê tổng kết"""
    print("\n" + "=" * 80)
    print("THỐNG KÊ TỔNG KẾT")
    print("=" * 80)

    total = len(results)
    optimal_count = sum(1 for r in results if r['status'] == 'Optimal')
    feasible_count = sum(1 for r in results if r['status'] == 'Feasible')
    timeout_count = sum(1 for r in results if r['status'] == 'Timeout')
    error_count = sum(1 for r in results if r['status'] == 'Error')
    infeasible_count = sum(1 for r in results if r['status'] == 'Infeasible')

    print(f"Tổng số instances: {total}")
    print(f"Optimal: {optimal_count} ({optimal_count / total * 100:.1f}%)")
    print(f"Feasible: {feasible_count} ({feasible_count / total * 100:.1f}%)")
    print(f"Timeout: {timeout_count} ({timeout_count / total * 100:.1f}%)")
    print(f"Error: {error_count} ({error_count / total * 100:.1f}%)")
    print(f"Infeasible: {infeasible_count} ({infeasible_count / total * 100:.1f}%)")

    # Thống kê thời gian
    valid_times = [float(r['time']) for r in results if r['time'] != 'N/A' and isinstance(r['time'], (int, float))]
    if valid_times:
        print(f"\nThống kê thời gian giải:")
        print(f"Trung bình: {sum(valid_times) / len(valid_times):.2f}s")
        print(f"Tối thiểu: {min(valid_times):.2f}s")
        print(f"Tối đa: {max(valid_times):.2f}s")

    # Top 10 instances khó nhất (thời gian cao nhất)
    print(f"\nTop 10 instances khó nhất:")
    print("-" * 50)
    sorted_results = sorted([r for r in results if r['time'] != 'N/A'],
                            key=lambda x: float(x['time']) if isinstance(x['time'], (int, float)) else 0,
                            reverse=True)

    for i, result in enumerate(sorted_results[:10], 1):
        print(f"{i:2d}. {result['instance']:<20} {result['time']:>8}s {result['status']}")


if __name__ == "__main__":
    main()