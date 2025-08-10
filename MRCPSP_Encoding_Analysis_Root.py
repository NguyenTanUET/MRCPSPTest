
"""
MRCPSP Encoding Analysis - Tách riêng các công thức encoding để phân tích
Chứa các method encode riêng biệt cho công thức 6.9, 6.10, 6.11, 6.12, 6.17
"""

import os
import time
from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42


class MRCPSPEncodingAnalyzer:
    """Class để phân tích riêng từng loại encoding"""

    def __init__(self, mm_reader):
        self.jobs = mm_reader.data['num_jobs']
        self.horizon = mm_reader.get_horizon()
        self.renewable_resources = mm_reader.data['num_renewable']
        self.nonrenewable_resources = mm_reader.data['num_nonrenewable']

        self.R_capacity = mm_reader.data['renewable_capacity']
        self.N_capacity = mm_reader.data['nonrenewable_capacity']

        self.precedence = mm_reader.data['precedence']
        self.job_modes = mm_reader.data['job_modes']

        # Tính time windows
        self.calculate_time_windows()

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

    def analyze_encoding_6_9_and_6_10(self):
        """Phân tích encoding cho công thức 6.9 (precedence) và 6.10 (mode selection)"""
        print("=" * 80)
        print("PHÂN TÍCH ENCODING CÔNG THỨC 6.9 (PRECEDENCE) VÀ 6.10 (MODE SELECTION)")
        print("=" * 80)

        # Khởi tạo
        cnf = CNF()
        vpool = IDPool()

        # Tạo variables
        s_vars = {}  # Start time variables
        sm_vars = {}  # Mode selection variables

        # 1. Tạo start time variables
        total_s_vars = 0
        for j in range(1, self.jobs + 1):
            s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = vpool.id(f's_{j}_{t}')
                s_vars[j][t] = var
                total_s_vars += 1

        # 2. Tạo mode selection variables
        total_sm_vars = 0
        for j in range(1, self.jobs + 1):
            sm_vars[j] = {}
            for m in range(len(self.job_modes[j])):
                var = vpool.id(f'sm_{j}_{m}')
                sm_vars[j][m] = var
                total_sm_vars += 1

        print(f"Variables được tạo:")
        print(f"  - Start time variables (s_j_t): {total_s_vars}")
        print(f"  - Mode selection variables (sm_j_m): {total_sm_vars}")
        print(f"  - Tổng variables: {total_s_vars + total_sm_vars}")

        # 3. Encode công thức 6.10 - Mode selection constraints
        clauses_6_10 = 0
        for j in range(1, self.jobs + 1):
            mode_vars = []
            for m in range(len(self.job_modes[j])):
                mode_vars.append(sm_vars[j][m])

            # Exactly one mode (công thức 6.17)
            # At least one
            cnf.append(mode_vars)
            clauses_6_10 += 1

            # At most one
            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    cnf.append([-mode_vars[i], -mode_vars[k]])
                    clauses_6_10 += 1

        # 4. Encode công thức 6.9 - Precedence constraints
        clauses_6_9 = 0
        for j in range(1, self.jobs + 1):
            if j not in self.precedence:
                continue

            for successor in self.precedence[j]:
                # Với mỗi mode của j
                for m_j in range(len(self.job_modes[j])):
                    duration_j = self.job_modes[j][m_j][0]

                    for t_j in range(self.ES[j], self.LS[j] + 1):
                        if t_j not in s_vars[j]:
                            continue

                        completion_j = t_j + duration_j

                        for t_s in range(self.ES[successor], min(completion_j, self.LS[successor] + 1)):
                            if t_s in s_vars[successor]:
                                cnf.append([
                                    -sm_vars[j][m_j],
                                    -s_vars[j][t_j],
                                    -s_vars[successor][t_s]
                                ])
                                clauses_6_9 += 1

        print(f"\nClauses được tạo:")
        print(f"  - Công thức 6.10 (Mode selection): {clauses_6_10} clauses")
        print(f"  - Công thức 6.9 (Precedence): {clauses_6_9} clauses")
        print(f"  - Tổng clauses: {clauses_6_10 + clauses_6_9}")

        return {
            'variables': total_s_vars + total_sm_vars,
            'clauses_6_9': clauses_6_9,
            'clauses_6_10': clauses_6_10,
            'total_clauses': clauses_6_9 + clauses_6_10,
            's_vars': total_s_vars,
            'sm_vars': total_sm_vars
        }

    def analyze_encoding_6_11_6_12_6_17(self):
        """Phân tích encoding cho công thức 6.11, 6.12, 6.17 (Resource constraints và Mode selection)"""
        print("\n" + "=" * 80)
        print("PHÂN TÍCH ENCODING CÔNG THỨC 6.11, 6.12, 6.17")
        print("=" * 80)

        # Khởi tạo
        cnf = CNF()
        vpool = IDPool()

        # Tạo variables
        sm_vars = {}  # Mode selection variables
        x_vars = {}   # Running variables
        s_vars = {}   # Start time variables

        # 1. Tạo start time variables
        total_s_vars = 0
        for j in range(1, self.jobs + 1):
            s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = vpool.id(f's_{j}_{t}')
                s_vars[j][t] = var
                total_s_vars += 1

        # 2. Tạo mode selection variables
        total_sm_vars = 0
        for j in range(1, self.jobs + 1):
            sm_vars[j] = {}
            for m in range(len(self.job_modes[j])):
                var = vpool.id(f'sm_{j}_{m}')
                sm_vars[j][m] = var
                total_sm_vars += 1

        # 3. Tạo running variables x_{i,t,o}
        total_x_vars = 0
        for j in range(1, self.jobs + 1):
            x_vars[j] = {}
            for t in range(self.horizon + 1):
                x_vars[j][t] = {}
                for m in range(len(self.job_modes[j])):
                    var = vpool.id(f'x_{j}_{t}_{m}')
                    x_vars[j][t][m] = var
                    total_x_vars += 1

        print(f"Variables được tạo:")
        print(f"  - Start time variables (s_j_t): {total_s_vars}")
        print(f"  - Mode selection variables (sm_j_m): {total_sm_vars}")
        print(f"  - Running variables (x_j_t_m): {total_x_vars}")
        print(f"  - Tổng variables: {total_s_vars + total_sm_vars + total_x_vars}")

        # 4. Encode công thức 6.17 - Mode selection (exactly one)
        clauses_6_17 = 0
        for j in range(1, self.jobs + 1):
            mode_vars = []
            for m in range(len(self.job_modes[j])):
                mode_vars.append(sm_vars[j][m])

            # At least one
            cnf.append(mode_vars)
            clauses_6_17 += 1

            # At most one
            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    cnf.append([-mode_vars[i], -mode_vars[k]])
                    clauses_6_17 += 1

        # 5. Encode running variable constraints (liên kết x với s và sm)
        clauses_running = 0
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
                for m in range(len(self.job_modes[j])):
                    duration = self.job_modes[j][m][0]

                    valid_starts = []
                    for t_start in range(max(self.ES[j], t - duration + 1), min(t + 1, self.LS[j] + 1)):
                        if t_start in s_vars[j] and t_start + duration > t:
                            valid_starts.append(s_vars[j][t_start])

                    if valid_starts:
                        # x_{j,t,m} => sm_{j,m}
                        cnf.append([-x_vars[j][t][m], sm_vars[j][m]])
                        clauses_running += 1

                        # x_{j,t,m} => OR(valid_starts)
                        cnf.append([-x_vars[j][t][m]] + valid_starts)
                        clauses_running += 1

                        # sm_{j,m} AND any valid_start => x_{j,t,m}
                        for start_var in valid_starts:
                            cnf.append([-sm_vars[j][m], -start_var, x_vars[j][t][m]])
                            clauses_running += 1
                    else:
                        # No valid starts => x_{j,t,m} = 0
                        cnf.append([-x_vars[j][t][m]])
                        clauses_running += 1

        # 6. Encode công thức 6.11 - Renewable resource constraints
        clauses_6_11 = 0
        pb_constraints_6_11 = 0
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
                resource_vars = []
                resource_weights = []

                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        if len(self.job_modes[j][m][1]) > k:
                            resource_req = self.job_modes[j][m][1][k]
                            if resource_req > 0:
                                resource_vars.append(x_vars[j][t][m])
                                resource_weights.append(resource_req)

                # PB constraint: sum <= capacity
                if resource_vars:
                    pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                               self.R_capacity[k], vpool=vpool)
                    # PBEnc.atmost trả về CNFPlus, cần convert thành clauses
                    pb_clauses = list(pb_constraint.clauses)
                    cnf.extend(pb_clauses)
                    clauses_6_11 += len(pb_clauses)
                    pb_constraints_6_11 += 1

        # 7. Encode công thức 6.12 - Non-renewable resource constraints
        clauses_6_12 = 0
        pb_constraints_6_12 = 0
        for k in range(self.nonrenewable_resources):
            resource_vars = []
            resource_weights = []

            for j in range(1, self.jobs + 1):
                for m in range(len(self.job_modes[j])):
                    resource_idx = self.renewable_resources + k
                    if len(self.job_modes[j][m][1]) > resource_idx:
                        resource_req = self.job_modes[j][m][1][resource_idx]
                        if resource_req > 0:
                            resource_vars.append(sm_vars[j][m])
                            resource_weights.append(resource_req)

            # PB constraint: total usage <= capacity
            if resource_vars:
                pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                           self.N_capacity[k], vpool=vpool)
                # PBEnc.atmost trả về CNFPlus, cần convert thành clauses
                pb_clauses = list(pb_constraint.clauses)
                cnf.extend(pb_clauses)
                clauses_6_12 += len(pb_clauses)
                pb_constraints_6_12 += 1

        print(f"\nClauses được tạo:")
        print(f"  - Công thức 6.17 (Mode selection exactly one): {clauses_6_17} clauses")
        print(f"  - Running variable constraints: {clauses_running} clauses")
        print(f"  - Công thức 6.11 (Renewable resources): {clauses_6_11} clauses ({pb_constraints_6_11} PB constraints)")
        print(f"  - Công thức 6.12 (Non-renewable resources): {clauses_6_12} clauses ({pb_constraints_6_12} PB constraints)")
        print(f"  - Tổng clauses: {clauses_6_17 + clauses_running + clauses_6_11 + clauses_6_12}")

        return {
            'variables': total_s_vars + total_sm_vars + total_x_vars,
            'clauses_6_17': clauses_6_17,
            'clauses_running': clauses_running,
            'clauses_6_11': clauses_6_11,
            'clauses_6_12': clauses_6_12,
            'pb_constraints_6_11': pb_constraints_6_11,
            'pb_constraints_6_12': pb_constraints_6_12,
            'total_clauses': clauses_6_17 + clauses_running + clauses_6_11 + clauses_6_12,
            's_vars': total_s_vars,
            'sm_vars': total_sm_vars,
            'x_vars': total_x_vars
        }

    def analyze_complete_encoding(self):
        """Phân tích complete encoding với tất cả constraints"""
        print("\n" + "=" * 80)
        print("PHÂN TÍCH COMPLETE ENCODING (TẤT CẢ CONSTRAINTS)")
        print("=" * 80)

        # Khởi tạo
        cnf = CNF()
        vpool = IDPool()

        # Tạo tất cả variables
        s_vars = {}   # Start time variables
        sm_vars = {}  # Mode selection variables
        x_vars = {}   # Running variables

        # 1. Start time variables
        total_s_vars = 0
        for j in range(1, self.jobs + 1):
            s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = vpool.id(f's_{j}_{t}')
                s_vars[j][t] = var
                total_s_vars += 1

        # 2. Mode selection variables
        total_sm_vars = 0
        for j in range(1, self.jobs + 1):
            sm_vars[j] = {}
            for m in range(len(self.job_modes[j])):
                var = vpool.id(f'sm_{j}_{m}')
                sm_vars[j][m] = var
                total_sm_vars += 1

        # 3. Running variables
        total_x_vars = 0
        for j in range(1, self.jobs + 1):
            x_vars[j] = {}
            for t in range(self.horizon + 1):
                x_vars[j][t] = {}
                for m in range(len(self.job_modes[j])):
                    var = vpool.id(f'x_{j}_{t}_{m}')
                    x_vars[j][t][m] = var
                    total_x_vars += 1

        total_vars = total_s_vars + total_sm_vars + total_x_vars

        # Đếm từng loại constraint
        clause_counts = {
            'start_time_exactly_one': 0,
            'mode_selection_exactly_one': 0,
            'precedence': 0,
            'running_variable_def': 0,
            'renewable_resource': 0,
            'nonrenewable_resource': 0
        }

        # Start time exactly one
        for j in range(1, self.jobs + 1):
            lits = []
            for t in range(self.ES[j], self.LS[j] + 1):
                if t in s_vars[j]:
                    lits.append(s_vars[j][t])

            if lits:
                cnf.append(lits)
                clause_counts['start_time_exactly_one'] += 1

                for i in range(len(lits)):
                    for k in range(i + 1, len(lits)):
                        cnf.append([-lits[i], -lits[k]])
                        clause_counts['start_time_exactly_one'] += 1

        # Mode selection exactly one
        for j in range(1, self.jobs + 1):
            mode_vars = []
            for m in range(len(self.job_modes[j])):
                mode_vars.append(sm_vars[j][m])

            cnf.append(mode_vars)
            clause_counts['mode_selection_exactly_one'] += 1

            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    cnf.append([-mode_vars[i], -mode_vars[k]])
                    clause_counts['mode_selection_exactly_one'] += 1

        # Precedence constraints
        for j in range(1, self.jobs + 1):
            if j not in self.precedence:
                continue

            for successor in self.precedence[j]:
                for m_j in range(len(self.job_modes[j])):
                    duration_j = self.job_modes[j][m_j][0]

                    for t_j in range(self.ES[j], self.LS[j] + 1):
                        if t_j not in s_vars[j]:
                            continue

                        completion_j = t_j + duration_j

                        for t_s in range(self.ES[successor], min(completion_j, self.LS[successor] + 1)):
                            if t_s in s_vars[successor]:
                                cnf.append([
                                    -sm_vars[j][m_j],
                                    -s_vars[j][t_j],
                                    -s_vars[successor][t_s]
                                ])
                                clause_counts['precedence'] += 1

        # Running variable definition
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
                for m in range(len(self.job_modes[j])):
                    duration = self.job_modes[j][m][0]

                    valid_starts = []
                    for t_start in range(max(self.ES[j], t - duration + 1), min(t + 1, self.LS[j] + 1)):
                        if t_start in s_vars[j] and t_start + duration > t:
                            valid_starts.append(s_vars[j][t_start])

                    if valid_starts:
                        cnf.append([-x_vars[j][t][m], sm_vars[j][m]])
                        clause_counts['running_variable_def'] += 1

                        cnf.append([-x_vars[j][t][m]] + valid_starts)
                        clause_counts['running_variable_def'] += 1

                        for start_var in valid_starts:
                            cnf.append([-sm_vars[j][m], -start_var, x_vars[j][t][m]])
                            clause_counts['running_variable_def'] += 1
                    else:
                        cnf.append([-x_vars[j][t][m]])
                        clause_counts['running_variable_def'] += 1

        # Renewable resource constraints
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
                resource_vars = []
                resource_weights = []

                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        if len(self.job_modes[j][m][1]) > k:
                            resource_req = self.job_modes[j][m][1][k]
                            if resource_req > 0:
                                resource_vars.append(x_vars[j][t][m])
                                resource_weights.append(resource_req)

                if resource_vars:
                    pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                               self.R_capacity[k], vpool=vpool)
                    pb_clauses = list(pb_constraint.clauses)
                    cnf.extend(pb_clauses)
                    clause_counts['renewable_resource'] += len(pb_clauses)

        # Non-renewable resource constraints
        for k in range(self.nonrenewable_resources):
            resource_vars = []
            resource_weights = []

            for j in range(1, self.jobs + 1):
                for m in range(len(self.job_modes[j])):
                    resource_idx = self.renewable_resources + k
                    if len(self.job_modes[j][m][1]) > resource_idx:
                        resource_req = self.job_modes[j][m][1][resource_idx]
                        if resource_req > 0:
                            resource_vars.append(sm_vars[j][m])
                            resource_weights.append(resource_req)

            if resource_vars:
                pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                           self.N_capacity[k], vpool=vpool)
                pb_clauses = list(pb_constraint.clauses)
                cnf.extend(pb_clauses)
                clause_counts['nonrenewable_resource'] += len(pb_clauses)

        total_clauses = sum(clause_counts.values())

        print(f"  - TỔNG VARIABLES: {total_vars}")

        print(f"  - TỔNG CLAUSES: {total_clauses}")

        return {
            'total_variables': total_vars,
            'total_clauses': total_clauses,
            'clause_breakdown': clause_counts,
            'variable_breakdown': {
                's_vars': total_s_vars,
                'sm_vars': total_sm_vars,
                'x_vars': total_x_vars
            }
        }


def analyze_instance(instance_file):
    """Phân tích một instance cụ thể"""
    print(f"\nPhân tích instance: {instance_file}")
    print("=" * 100)

    # Import data reader từ file chính
    import sys
    sys.path.append('.')
    from No_Cloud_MRCPSP_G42_600s_1 import MRCPSPDataReader

    # Đọc dữ liệu
    reader = MRCPSPDataReader(instance_file)

    print(f"Thông tin instance:")
    print(f"  - Số jobs: {reader.data['num_jobs']}")
    print(f"  - Horizon: {reader.get_horizon()}")
    print(f"  - Renewable resources: {reader.data['num_renewable']}")
    print(f"  - Non-renewable resources: {reader.data['num_nonrenewable']}")

    # Tạo analyzer
    analyzer = MRCPSPEncodingAnalyzer(reader)

    # Phân tích từng nhóm
    result_6_9_6_10 = analyzer.analyze_encoding_6_9_and_6_10()
    result_6_11_6_12_6_17 = analyzer.analyze_encoding_6_11_6_12_6_17()
    result_complete = analyzer.analyze_complete_encoding()

    return {
        'instance_file': instance_file,
        'instance_info': {
            'jobs': reader.data['num_jobs'],
            'horizon': reader.get_horizon(),
            'renewable_resources': reader.data['num_renewable'],
            'nonrenewable_resources': reader.data['num_nonrenewable']
        },
        'encoding_6_9_6_10': result_6_9_6_10,
        'encoding_6_11_6_12_6_17': result_6_11_6_12_6_17,
        'complete_encoding': result_complete
    }


def main():
    """Test với một instance mẫu"""
    import glob

    # Tìm file test
    test_files = glob.glob("data/j30/*.mm")
    if not test_files:
        print("Không tìm thấy file test trong data/j30/")
        return

    # Lấy file đầu tiên để test
    test_file = test_files[0]

    # Phân tích
    results = analyze_instance(test_file)

    # Xuất kết quả tổng hợp
    print("\n" + "=" * 100)
    print("TỔNG HỢP KẾT QUẢ PHÂN TÍCH")
    print("=" * 100)

    print(f"Instance: {results['instance_file']}")
    info = results['instance_info']
    print(f"Jobs: {info['jobs']}, Horizon: {info['horizon']}, R: {info['renewable_resources']}, N: {info['nonrenewable_resources']}")

    print(f"\nSo sánh số lượng variables và clauses:")
    enc1 = results['encoding_6_9_6_10']
    enc2 = results['encoding_6_11_6_12_6_17']
    enc3 = results['complete_encoding']

    print(f"  Encoding 6.9 + 6.10:")
    print(f"    Variables: {enc1['variables']}, Clauses: {enc1['total_clauses']}")

    print(f"  Encoding 6.11 + 6.12 + 6.17:")
    print(f"    Variables: {enc2['variables']}, Clauses: {enc2['total_clauses']}")

    print(f"  Complete Encoding:")
    print(f"    Variables: {enc3['total_variables']}, Clauses: {enc3['total_clauses']}")


if __name__ == "__main__":
    main()