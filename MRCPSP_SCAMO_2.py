"""
MRCPSP Block-Based SCAMO Encoding - Optimized Version
Giảm thiểu số clauses bằng cách áp dụng block-based encoding đúng cách
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
import time
import math


class MRCPSPBlockBasedStaircase:
    """MRCPSP Encoder với block-based SCAMO optimized"""

    def __init__(self, mm_reader, block_width=10):
        self.cnf = CNF()
        self.vpool = IDPool()

        # Block width cho encoding
        self.block_width = block_width

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

        # Block structures
        self.start_time_blocks = {}  # {job: blocks}
        self.register_bits = {}

        # Statistics
        self.stats = {
            'variables': 0,
            'clauses': 0,
            'amo_blocks': 0,
            'amz_blocks': 0,
            'register_bits': 0,
            'connection_clauses': 0,
            'total_blocks': 0
        }

    def calculate_time_windows(self):
        """Tính ES và LS cho mỗi job"""
        self.ES = {}
        self.LS = {}

        for j in range(1, self.jobs + 1):
            self.ES[j] = 0
            self.LS[j] = self.horizon

        # Forward pass
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

        # Backward pass
        for j in range(1, self.jobs + 1):
            if j in self.job_modes and self.job_modes[j]:
                max_duration = max(mode[0] for mode in self.job_modes[j])
                self.LS[j] = min(self.LS[j], self.horizon - max_duration)

    def create_variables(self):
        """Create all variables"""
        # s_{j,t} variables
        self.s_vars = {}
        for j in range(1, self.jobs + 1):
            self.s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = self.vpool.id(f's_{j}_{t}')
                self.s_vars[j][t] = var
                self.stats['variables'] += 1

        # sm_{j,m} variables
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

    def create_blocks_for_variables(self, variables, block_id_prefix):
        """
        Generic function to create blocks for a list of variables
        """
        if not variables:
            return []

        blocks = []
        num_blocks = (len(variables) + self.block_width - 1) // self.block_width

        for i in range(num_blocks):
            start_idx = i * self.block_width
            end_idx = min(start_idx + self.block_width, len(variables))

            block_vars = variables[start_idx:end_idx]

            # First and last blocks are AMO, middle blocks can be AMZ
            if i == 0 or i == num_blocks - 1:
                block_type = 'AMO'
                self.stats['amo_blocks'] += 1
            else:
                block_type = 'AMZ'
                self.stats['amz_blocks'] += 1

            blocks.append({
                'id': f"{block_id_prefix}_{i}",
                'vars': block_vars,
                'type': block_type
            })

            self.stats['total_blocks'] += 1

        return blocks

    def encode_amo_block(self, block):
        """Encode AMO block using staircase"""
        block_vars = block['vars']
        block_id = block['id']

        if len(block_vars) <= 1:
            return []

        # Create register bits
        register_bits = [block_vars[0]]  # R_1 = x_1

        for j in range(2, len(block_vars) + 1):
            reg_var = self.vpool.id(f'R_{block_id}_{j}')
            register_bits.append(reg_var)
            self.stats['register_bits'] += 1

        n = len(block_vars)

        # 4 formulas for AMO
        for j in range(1, n):
            # Formula 1: x_j → R_j
            self.cnf.append([-block_vars[j], register_bits[j]])
            # Formula 2: R_{j-1} → R_j
            self.cnf.append([-register_bits[j-1], register_bits[j]])
            # Formula 3: ¬x_j ∧ ¬R_{j-1} → ¬R_j
            self.cnf.append([block_vars[j], register_bits[j-1], -register_bits[j]])
            # Formula 4: x_j → ¬R_{j-1}
            self.cnf.append([-block_vars[j], -register_bits[j-1]])

            self.stats['clauses'] += 4

        self.register_bits[block_id] = register_bits
        return register_bits

    def encode_amz_block(self, block):
        """Encode AMZ block (no formula 4)"""
        block_vars = block['vars']
        block_id = block['id']

        if len(block_vars) <= 1:
            return []

        # Create register bits
        register_bits = [block_vars[0]]

        for j in range(2, len(block_vars) + 1):
            reg_var = self.vpool.id(f'R_{block_id}_{j}')
            register_bits.append(reg_var)
            self.stats['register_bits'] += 1

        n = len(block_vars)

        # 3 formulas for AMZ (no formula 4)
        for j in range(1, n):
            self.cnf.append([-block_vars[j], register_bits[j]])
            self.cnf.append([-register_bits[j-1], register_bits[j]])
            self.cnf.append([block_vars[j], register_bits[j-1], -register_bits[j]])

            self.stats['clauses'] += 3

        self.register_bits[block_id] = register_bits
        return register_bits

    def connect_blocks(self, block1_id, block2_id):
        """Connect two AMO blocks"""
        if block1_id not in self.register_bits or block2_id not in self.register_bits:
            return

        reg1 = self.register_bits[block1_id]
        reg2 = self.register_bits[block2_id]

        if reg1 and reg2:
            # Connect last of block1 with first of block2
            self.cnf.append([-reg1[-1], -reg2[0]])
            self.stats['connection_clauses'] += 1

    def add_start_time_constraints(self):
        """Start time constraints with blocks"""
        for j in range(1, self.jobs + 1):
            # Get all start time variables for job j
            vars_list = []
            for t in range(self.ES[j], self.LS[j] + 1):
                if t in self.s_vars[j]:
                    vars_list.append(self.s_vars[j][t])

            if not vars_list:
                continue

            # Create blocks
            blocks = self.create_blocks_for_variables(vars_list, f"start_{j}")
            self.start_time_blocks[j] = blocks

            # Encode blocks
            amo_blocks = []
            for block in blocks:
                if block['type'] == 'AMO':
                    self.encode_amo_block(block)
                    amo_blocks.append(block['id'])
                else:  # AMZ
                    self.encode_amz_block(block)

            # Connect AMO blocks
            for i in range(len(amo_blocks) - 1):
                self.connect_blocks(amo_blocks[i], amo_blocks[i+1])

            # At least one constraint
            self.cnf.append(vars_list)
            self.stats['clauses'] += 1

    def add_mode_selection_constraints(self):
        """Mode selection with blocks for jobs with many modes"""
        for j in range(1, self.jobs + 1):
            mode_vars = [self.sm_vars[j][m] for m in range(len(self.job_modes[j]))]

            # At least one
            self.cnf.append(mode_vars)
            self.stats['clauses'] += 1

            # At most one - use blocks if many modes, otherwise pairwise
            if len(mode_vars) > 5:  # Threshold for using blocks
                blocks = self.create_blocks_for_variables(mode_vars, f"mode_{j}")

                for block in blocks:
                    if block['type'] == 'AMO':
                        self.encode_amo_block(block)
                    else:
                        self.encode_amz_block(block)

                # Connect blocks if multiple AMO blocks
                amo_blocks = [b['id'] for b in blocks if b['type'] == 'AMO']
                for i in range(len(amo_blocks) - 1):
                    self.connect_blocks(amo_blocks[i], amo_blocks[i+1])
            else:
                # Pairwise for small number of modes
                for i in range(len(mode_vars)):
                    for k in range(i + 1, len(mode_vars)):
                        self.cnf.append([-mode_vars[i], -mode_vars[k]])
                        self.stats['clauses'] += 1

    def add_precedence_constraints(self):
        """Precedence constraints - optimized"""
        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence:
                continue

            for succ in self.precedence[pred]:
                for m_pred in range(len(self.job_modes[pred])):
                    duration_pred = self.job_modes[pred][m_pred][0]

                    for t_pred in range(self.ES[pred], self.LS[pred] + 1):
                        if t_pred not in self.s_vars[pred]:
                            continue

                        earliest_succ = t_pred + duration_pred

                        # Only add constraints for feasible violations
                        for t_succ in range(self.ES[succ], min(earliest_succ, self.LS[succ] + 1)):
                            if t_succ in self.s_vars[succ]:
                                self.cnf.append([
                                    -self.sm_vars[pred][m_pred],
                                    -self.s_vars[pred][t_pred],
                                    -self.s_vars[succ][t_succ]
                                ])
                                self.stats['clauses'] += 1

    def add_process_variable_constraints(self):
        """Process variable constraints"""
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
                        self.cnf.append([-self.u_vars[j][t][m]] + valid_starts)

                        for start_var in valid_starts:
                            self.cnf.append([-self.sm_vars[j][m], -start_var, self.u_vars[j][t][m]])

                        self.stats['clauses'] += (2 + len(valid_starts))
                    else:
                        self.cnf.append([-self.u_vars[j][t][m]])
                        self.stats['clauses'] += 1

    def add_renewable_resource_constraints(self):
        """Renewable resource constraints"""
        for k in range(self.renewable_resources):
            for t in range(self.horizon + 1):
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
                                                self.R_capacity[k], vpool=self.vpool)
                    self.cnf.extend(pb_constraint)

    def add_nonrenewable_resource_constraints(self):
        """Non-renewable resource constraints"""
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

            if resource_vars:
                pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                           self.N_capacity[k], vpool=self.vpool)
                self.cnf.extend(pb_constraint)

    def add_makespan_constraint(self, makespan):
        """Makespan constraint"""
        sink_job = self.jobs

        for t in range(makespan + 1, self.LS[sink_job] + 1):
            if t in self.s_vars[sink_job]:
                self.cnf.append([-self.s_vars[sink_job][t]])
                self.stats['clauses'] += 1

    def encode(self, makespan=None):
        """Encode with optimized SCAMO"""
        print("\n=== ENCODING WITH OPTIMIZED SCAMO ===")

        print("Creating variables...")
        self.create_variables()

        print("Adding start time constraints with blocks...")
        self.add_start_time_constraints()

        print("Adding mode selection constraints...")
        self.add_mode_selection_constraints()

        print("Adding precedence constraints...")
        self.add_precedence_constraints()

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
        print(f"Total blocks: {self.stats['total_blocks']}")
        print(f"  - AMO blocks: {self.stats['amo_blocks']}")
        print(f"  - AMZ blocks: {self.stats['amz_blocks']}")
        print(f"Connection clauses: {self.stats['connection_clauses']}")

        return self.cnf

    def solve(self, makespan):
        """Solve with given makespan"""
        print(f"\n--- Solving with makespan = {makespan} ---")

        # Reset
        self.cnf = CNF()
        self.vpool = IDPool()
        self.start_time_blocks = {}
        self.register_bits = {}
        self.stats = {
            'variables': 0,
            'clauses': 0,
            'amo_blocks': 0,
            'amz_blocks': 0,
            'register_bits': 0,
            'connection_clauses': 0,
            'total_blocks': 0
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
        """Find optimal makespan"""
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

    def test_precedence_aware_encoding(test_file=None):
        """Test the precedence-aware block encoding"""

        try:
            from MRCPSP_Basic import MRCPSPDataReader
        except:
            print("Cannot import MRCPSPDataReader")
            return None, None

        if test_file is None:
            test_file = "data/j30/j301_1.mm"

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
        test_precedence_aware_encoding()
        print("\n" + "=" * 100)
