"""
MRCPSP Staircase Encoding Analysis
So sánh Staircase Encoding với Standard Encoding về số lượng variables và clauses
"""

import os
from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool


class MRCPSPStaircaseAnalyzer:
    """Class để phân tích Staircase Encoding cho MRCPSP"""

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

    def analyze_staircase_precedence_encoding(self):
        """Phân tích Staircase Encoding cho precedence constraints"""
        print("=" * 80)
        print("PHÂN TÍCH STAIRCASE ENCODING CHO PRECEDENCE CONSTRAINTS")
        print("=" * 80)

        # Khởi tạo
        cnf = CNF()
        vpool = IDPool()

        # Register cache
        forward_register = {}
        register_vars_count = 0
        register_clauses_count = 0

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

        print(f"Variables cơ bản:")
        print(f"  - Start time variables (s_j_t): {total_s_vars}")
        print(f"  - Mode selection variables (sm_j_m): {total_sm_vars}")

        # 3. Simulate staircase register creation
        def get_forward_staircase_register(job, start, end):
            """Simulate register creation and count variables/clauses"""
            nonlocal register_vars_count, register_clauses_count

            if start >= end:
                return None

            # Clamp to valid range
            start = max(start, self.ES[job])
            end = min(end, self.LS[job] + 1)

            if start >= end:
                return None

            key = (job, start, end)
            if key in forward_register:
                return forward_register[key]

            # Count time variables in range
            time_vars_count = 0
            for t in range(start, end):
                if t <= self.LS[job]:
                    time_vars_count += 1

            if time_vars_count == 0:
                return None

            if time_vars_count == 1:
                # No register needed
                forward_register[key] = f'single_var_{job}_{start}'
                return forward_register[key]

            # Need register variable
            register_vars_count += 1
            reg_var = f'reg_{job}_{start}_{end}'
            forward_register[key] = reg_var

            # Count clauses for register definition
            # reg => OR(s_vars)
            register_clauses_count += 1
            # Each s_var => reg
            register_clauses_count += time_vars_count

            return reg_var

        # 4. Count precedence clauses with staircase
        precedence_clauses_staircase = 0

        for predecessor in range(1, self.jobs + 1):
            if predecessor not in self.precedence:
                continue

            for successor in self.precedence[predecessor]:
                # For each possible start time k of successor
                for k in range(self.ES[successor], self.LS[successor] + 1):
                    # Get register for successor starting by time k
                    reg_succ = get_forward_staircase_register(successor, self.ES[successor], k + 1)

                    if not reg_succ:
                        continue

                    # For each mode of predecessor
                    for m_pred in range(len(self.job_modes[predecessor])):
                        duration_pred = self.job_modes[predecessor][m_pred][0]

                        # If predecessor finishes after k, successor cannot start before k
                        latest_start_pred = k - duration_pred

                        if latest_start_pred < self.ES[predecessor]:
                            # Predecessor cannot finish by time k with this mode
                            precedence_clauses_staircase += 1
                        else:
                            # Check specific start times
                            for t_pred in range(latest_start_pred + 1,
                                              min(self.LS[predecessor] + 1, k + 1)):
                                if t_pred <= self.LS[predecessor]:
                                    precedence_clauses_staircase += 1

        print(f"\nStaircase registers:")
        print(f"  - Số register variables được tạo: {register_vars_count}")
        print(f"  - Số clauses để define registers: {register_clauses_count}")

        print(f"\nPrecedence constraints:")
        print(f"  - Số clauses cho precedence (với staircase): {precedence_clauses_staircase}")

        total_vars = total_s_vars + total_sm_vars + register_vars_count
        total_clauses = register_clauses_count + precedence_clauses_staircase

        print(f"\nTổng cộng:")
        print(f"  - Tổng variables: {total_vars}")
        print(f"  - Tổng clauses (chỉ precedence + registers): {total_clauses}")

        return {
            'variables': total_vars,
            'base_vars': total_s_vars + total_sm_vars,
            'register_vars': register_vars_count,
            'precedence_clauses': precedence_clauses_staircase,
            'register_clauses': register_clauses_count,
            'total_clauses': total_clauses
        }

    def analyze_complete_staircase_encoding(self):
        """Phân tích complete Staircase Encoding với tất cả constraints"""
        print("\n" + "=" * 80)
        print("PHÂN TÍCH COMPLETE STAIRCASE ENCODING")
        print("=" * 80)

        # Khởi tạo
        cnf = CNF()
        vpool = IDPool()

        # Register cache
        forward_register = {}
        register_vars_count = 0
        register_clauses_count = 0

        # Tạo tất cả variables
        s_vars = {}   # Start time variables
        sm_vars = {}  # Mode selection variables
        u_vars = {}   # Process variables (thay cho x_vars)

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

        # 3. Process variables (u_{j,t,m})
        total_u_vars = 0
        for j in range(1, self.jobs + 1):
            u_vars[j] = {}
            for t in range(self.horizon + 1):
                u_vars[j][t] = {}
                for m in range(len(self.job_modes[j])):
                    # Only create if job can be running at time t with mode m
                    duration = self.job_modes[j][m][0]
                    earliest_start = max(0, t - duration + 1)
                    latest_start = t

                    if earliest_start <= self.LS[j] and latest_start >= self.ES[j]:
                        var = vpool.id(f'u_{j}_{t}_{m}')
                        u_vars[j][t][m] = var
                        total_u_vars += 1

        # Đếm từng loại constraint
        clause_counts = {
            'start_time_exactly_one': 0,
            'mode_selection_exactly_one': 0,
            'precedence_staircase': 0,
            'register_definition': 0,
            'process_variable_def': 0,
            'renewable_resource': 0,
            'nonrenewable_resource': 0
        }

        # Start time exactly one
        for j in range(1, self.jobs + 1):
            lits_count = 0
            for t in range(self.ES[j], self.LS[j] + 1):
                if t in s_vars[j]:
                    lits_count += 1

            if lits_count > 0:
                # At least one
                clause_counts['start_time_exactly_one'] += 1
                # At most one: C(n,2) clauses
                clause_counts['start_time_exactly_one'] += (lits_count * (lits_count - 1)) // 2

        # Mode selection exactly one
        for j in range(1, self.jobs + 1):
            mode_count = len(self.job_modes[j])
            # At least one
            clause_counts['mode_selection_exactly_one'] += 1
            # At most one: C(n,2) clauses
            clause_counts['mode_selection_exactly_one'] += (mode_count * (mode_count - 1)) // 2

        # Staircase register creation simulation
        def get_forward_staircase_register(job, start, end):
            nonlocal register_vars_count, clause_counts

            if start >= end:
                return None

            start = max(start, self.ES[job])
            end = min(end, self.LS[job] + 1)

            if start >= end:
                return None

            key = (job, start, end)
            if key in forward_register:
                return forward_register[key]

            time_vars_count = min(end - start, self.LS[job] - start + 1)

            if time_vars_count <= 0:
                return None

            if time_vars_count == 1:
                forward_register[key] = f'single_var_{job}_{start}'
                return forward_register[key]

            register_vars_count += 1
            reg_var = f'reg_{job}_{start}_{end}'
            forward_register[key] = reg_var

            # Register definition clauses
            clause_counts['register_definition'] += 1  # reg => OR(vars)
            clause_counts['register_definition'] += time_vars_count  # each var => reg

            return reg_var

        # Precedence constraints with staircase
        for predecessor in range(1, self.jobs + 1):
            if predecessor not in self.precedence:
                continue

            for successor in self.precedence[predecessor]:
                for k in range(self.ES[successor], self.LS[successor] + 1):
                    reg_succ = get_forward_staircase_register(successor, self.ES[successor], k + 1)

                    if not reg_succ:
                        continue

                    for m_pred in range(len(self.job_modes[predecessor])):
                        duration_pred = self.job_modes[predecessor][m_pred][0]
                        latest_start_pred = k - duration_pred

                        if latest_start_pred < self.ES[predecessor]:
                            clause_counts['precedence_staircase'] += 1
                        else:
                            for t_pred in range(latest_start_pred + 1,
                                              min(self.LS[predecessor] + 1, k + 1)):
                                if t_pred <= self.LS[predecessor]:
                                    clause_counts['precedence_staircase'] += 1

        # Process variable definition
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
                for m in range(len(self.job_modes[j])):
                    if m not in u_vars[j][t]:
                        continue

                    duration = self.job_modes[j][m][0]

                    # Count valid start times
                    valid_starts_count = 0
                    for t_start in range(max(self.ES[j], t - duration + 1),
                                       min(self.LS[j] + 1, t + 1)):
                        if t_start <= self.LS[j] and t_start + duration > t:
                            valid_starts_count += 1

                    if valid_starts_count > 0:
                        # u => sm
                        clause_counts['process_variable_def'] += 1
                        # u => OR(starts)
                        clause_counts['process_variable_def'] += 1
                        # sm AND start => u (for each valid start)
                        clause_counts['process_variable_def'] += valid_starts_count
                    else:
                        # u must be false
                        clause_counts['process_variable_def'] += 1

        # Resource constraints (simulate PB encoding)
        # Renewable
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
                resource_vars_count = 0

                for j in range(1, self.jobs + 1):
                    for m in range(len(self.job_modes[j])):
                        if m in u_vars[j][t] and len(self.job_modes[j][m][1]) > k:
                            if self.job_modes[j][m][1][k] > 0:
                                resource_vars_count += 1

                if resource_vars_count > 0:
                    # Estimate PB encoding clauses (rough approximation)
                    clause_counts['renewable_resource'] += resource_vars_count * 3

        # Non-renewable
        for k in range(self.nonrenewable_resources):
            resource_vars_count = 0

            for j in range(1, self.jobs + 1):
                for m in range(len(self.job_modes[j])):
                    resource_idx = self.renewable_resources + k
                    if len(self.job_modes[j][m][1]) > resource_idx:
                        if self.job_modes[j][m][1][resource_idx] > 0:
                            resource_vars_count += 1

            if resource_vars_count > 0:
                # Estimate PB encoding clauses
                clause_counts['nonrenewable_resource'] += resource_vars_count * 3

        total_vars = total_s_vars + total_sm_vars + total_u_vars + register_vars_count
        total_clauses = sum(clause_counts.values())

        print(f"Variables:")
        print(f"  - Start time vars (s): {total_s_vars}")
        print(f"  - Mode selection vars (sm): {total_sm_vars}")
        print(f"  - Process vars (u): {total_u_vars}")
        print(f"  - Staircase register vars: {register_vars_count}")
        print(f"  - TỔNG VARIABLES: {total_vars}")

        print(f"\nClauses:")
        for constraint_type, count in clause_counts.items():
            print(f"  - {constraint_type}: {count}")
        print(f"  - TỔNG CLAUSES: {total_clauses}")

        return {
            'total_variables': total_vars,
            'total_clauses': total_clauses,
            'clause_breakdown': clause_counts,
            'variable_breakdown': {
                's_vars': total_s_vars,
                'sm_vars': total_sm_vars,
                'u_vars': total_u_vars,
                'register_vars': register_vars_count
            }
        }


def compare_standard_vs_staircase(instance_file):
    """So sánh Standard Encoding với Staircase Encoding"""
    print(f"\n{'='*100}")
    print(f"SO SÁNH STANDARD vs STAIRCASE ENCODING")
    print(f"Instance: {instance_file}")
    print(f"{'='*100}")

    # Import necessary modules
    import sys
    sys.path.append('.')

    # Import standard analyzer
    from MRCPSP_Encoding_Analysis_Script import MRCPSPEncodingAnalyzer

    # Import data reader
    try:
        from MRCPSP_Basic import MRCPSPDataReader
    except:
        try:
            from No_Cloud_MRCPSP_G42_600s_1 import MRCPSPDataReader
        except:
            print("Cannot import MRCPSPDataReader")
            return

    # Read data
    reader = MRCPSPDataReader(instance_file)

    print(f"\nThông tin instance:")
    print(f"  - Số jobs: {reader.data['num_jobs']}")
    print(f"  - Horizon: {reader.get_horizon()}")
    print(f"  - Renewable resources: {reader.data['num_renewable']}")
    print(f"  - Non-renewable resources: {reader.data['num_nonrenewable']}")

    # Standard encoding analysis
    print("\n" + "="*80)
    print("STANDARD ENCODING ANALYSIS")
    print("="*80)

    standard_analyzer = MRCPSPEncodingAnalyzer(reader)
    standard_6_9_6_10 = standard_analyzer.analyze_encoding_6_9_and_6_10()
    standard_complete = standard_analyzer.analyze_complete_encoding()

    # Staircase encoding analysis
    print("\n" + "="*80)
    print("STAIRCASE ENCODING ANALYSIS")
    print("="*80)

    staircase_analyzer = MRCPSPStaircaseAnalyzer(reader)
    staircase_precedence = staircase_analyzer.analyze_staircase_precedence_encoding()
    staircase_complete = staircase_analyzer.analyze_complete_staircase_encoding()

    # Comparison results
    print("\n" + "="*100)
    print("KẾT QUẢ SO SÁNH")
    print("="*100)

    print("\n1. SO SÁNH PRECEDENCE CONSTRAINTS:")
    print(f"   Standard (formula 6.9):")
    print(f"     - Precedence clauses: {standard_6_9_6_10['clauses_6_9']}")
    print(f"   Staircase:")
    print(f"     - Precedence clauses: {staircase_precedence['precedence_clauses']}")
    print(f"     - Register definition clauses: {staircase_precedence['register_clauses']}")
    print(f"     - Total: {staircase_precedence['total_clauses']}")

    prec_reduction = ((standard_6_9_6_10['clauses_6_9'] - staircase_precedence['total_clauses']) /
                     standard_6_9_6_10['clauses_6_9'] * 100) if standard_6_9_6_10['clauses_6_9'] > 0 else 0

    print(f"   Giảm clauses: {prec_reduction:.1f}%")

    print("\n2. SO SÁNH COMPLETE ENCODING:")
    print(f"   Standard:")
    print(f"     - Total variables: {standard_complete['total_variables']}")
    print(f"     - Total clauses: {standard_complete['total_clauses']}")
    print(f"   Staircase:")
    print(f"     - Total variables: {staircase_complete['total_variables']}")
    print(f"       (includes {staircase_complete['variable_breakdown']['register_vars']} register vars)")
    print(f"     - Total clauses: {staircase_complete['total_clauses']}")

    var_increase = ((staircase_complete['total_variables'] - standard_complete['total_variables']) /
                   standard_complete['total_variables'] * 100)
    clause_reduction = ((standard_complete['total_clauses'] - staircase_complete['total_clauses']) /
                       standard_complete['total_clauses'] * 100) if standard_complete['total_clauses'] > 0 else 0

    print(f"   Variables: {'tăng' if var_increase > 0 else 'giảm'} {abs(var_increase):.1f}%")
    print(f"   Clauses: {'giảm' if clause_reduction > 0 else 'tăng'} {abs(clause_reduction):.1f}%")

    # Detailed breakdown
    print("\n3. PHÂN TÍCH CHI TIẾT CLAUSES (Staircase):")
    for constraint_type, count in staircase_complete['clause_breakdown'].items():
        percentage = (count / staircase_complete['total_clauses'] * 100) if staircase_complete['total_clauses'] > 0 else 0
        print(f"   - {constraint_type}: {count} ({percentage:.1f}%)")

    return {
        'standard': {
            'precedence_clauses': standard_6_9_6_10['clauses_6_9'],
            'total_variables': standard_complete['total_variables'],
            'total_clauses': standard_complete['total_clauses']
        },
        'staircase': {
            'precedence_clauses': staircase_precedence['precedence_clauses'],
            'register_clauses': staircase_precedence['register_clauses'],
            'total_variables': staircase_complete['total_variables'],
            'total_clauses': staircase_complete['total_clauses']
        },
        'improvements': {
            'precedence_reduction': prec_reduction,
            'variable_change': var_increase,
            'clause_reduction': clause_reduction
        }
    }


def main():
    """Test comparison"""
    import glob

    # Find test file
    test_files = glob.glob("data/j102_2.mm")
    if not test_files:
        test_files = glob.glob("data/j10/*.mm")
    if not test_files:
        print("Không tìm thấy file test!")
        return

    test_file = test_files[0]

    # Run comparison
    results = compare_standard_vs_staircase(test_file)

    # Summary table
    print("\n" + "="*100)
    print("BẢNG TÓM TẮT")
    print("="*100)

    print(f"\n{'Metric':<40} {'Standard':<20} {'Staircase':<20} {'Change':<20}")
    print("-"*100)

    print(f"{'Precedence clauses':<40} {results['standard']['precedence_clauses']:<20} "
          f"{results['staircase']['precedence_clauses'] + results['staircase']['register_clauses']:<20} "
          f"{results['improvements']['precedence_reduction']:.1f}% reduction")

    print(f"{'Total variables':<40} {results['standard']['total_variables']:<20} "
          f"{results['staircase']['total_variables']:<20} "
          f"{abs(results['improvements']['variable_change']):.1f}% "
          f"{'increase' if results['improvements']['variable_change'] > 0 else 'decrease'}")

    print(f"{'Total clauses':<40} {results['standard']['total_clauses']:<20} "
          f"{results['staircase']['total_clauses']:<20} "
          f"{abs(results['improvements']['clause_reduction']):.1f}% "
          f"{'reduction' if results['improvements']['clause_reduction'] > 0 else 'increase'}")


if __name__ == "__main__":
    main()