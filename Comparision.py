"""
So sánh số biến và mệnh đề giữa Basic Encoding và SCAMO Block-based Encoding
Chỉ tạo encoding, không giải bài toán
"""

from MRCPSP_Basic import MRCPSPDataReader
from MRCPSP_SCAMO_4 import MRCPSPBlockBasedStaircase
from pysat.formula import CNF, IDPool
from pysat.pb import PBEnc
import time
import sys


class BasicEncoder:
    """Basic MRCPSP Encoder (Traditional approach) - chỉ tạo encoding"""

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

        # Statistics
        self.stats = {
            'start_time_vars': 0,
            'mode_vars': 0,
            'running_vars': 0,
            'total_vars': 0,
            'start_time_clauses': 0,
            'mode_clauses': 0,
            'precedence_clauses': 0,
            'running_clauses': 0,
            'resource_clauses': 0,
            'makespan_clauses': 0,
            'total_clauses': 0
        }

    def calculate_time_windows(self):
        """Calculate ES and LS for each job"""
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
            if self.job_modes[j]:
                max_duration = max(mode[0] for mode in self.job_modes[j])
                self.LS[j] = self.horizon - max_duration

    def create_variables(self):
        """Create all variables"""
        # s_{j,t} variables for start times
        self.s_vars = {}
        for j in range(1, self.jobs + 1):
            self.s_vars[j] = {}
            for t in range(self.ES[j], self.LS[j] + 1):
                var = self.vpool.id(f's_{j}_{t}')
                self.s_vars[j][t] = var
                self.stats['start_time_vars'] += 1

        # sm_{j,m} variables for modes
        self.sm_vars = {}
        for j in range(1, self.jobs + 1):
            self.sm_vars[j] = {}
            for m in range(len(self.job_modes[j])):
                var = self.vpool.id(f'sm_{j}_{m}')
                self.sm_vars[j][m] = var
                self.stats['mode_vars'] += 1

        # x_{j,t,m} running variables
        self.x_vars = {}
        for j in range(1, self.jobs + 1):
            self.x_vars[j] = {}
            for t in range(self.horizon + 1):
                self.x_vars[j][t] = {}
                for m in range(len(self.job_modes[j])):
                    var = self.vpool.id(f'x_{j}_{t}_{m}')
                    self.x_vars[j][t][m] = var
                    self.stats['running_vars'] += 1

    def add_start_time_constraints(self):
        """Exactly one start time per job"""
        for j in range(1, self.jobs + 1):
            lits = [self.s_vars[j][t] for t in range(self.ES[j], self.LS[j] + 1)
                   if t in self.s_vars[j]]

            if lits:
                # At least one
                self.cnf.append(lits)
                self.stats['start_time_clauses'] += 1

                # At most one (pairwise)
                for i in range(len(lits)):
                    for k in range(i + 1, len(lits)):
                        self.cnf.append([-lits[i], -lits[k]])
                        self.stats['start_time_clauses'] += 1

    def add_mode_selection_constraints(self):
        """Exactly one mode per job"""
        for j in range(1, self.jobs + 1):
            mode_vars = [self.sm_vars[j][m] for m in range(len(self.job_modes[j]))]

            # At least one
            self.cnf.append(mode_vars)
            self.stats['mode_clauses'] += 1

            # At most one
            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    self.cnf.append([-mode_vars[i], -mode_vars[k]])
                    self.stats['mode_clauses'] += 1

    def add_precedence_constraints(self):
        """Precedence constraints"""
        for j in range(1, self.jobs + 1):
            if j not in self.precedence:
                continue

            for successor in self.precedence[j]:
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
                                self.stats['precedence_clauses'] += 1

    def add_running_variable_constraints(self):
        """Define running variables"""
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
                for m in range(len(self.job_modes[j])):
                    duration = self.job_modes[j][m][0]

                    valid_starts = []
                    for t_start in range(max(self.ES[j], t - duration + 1),
                                       min(t + 1, self.LS[j] + 1)):
                        if t_start in self.s_vars[j] and t_start + duration > t:
                            valid_starts.append(self.s_vars[j][t_start])

                    if valid_starts:
                        self.cnf.append([-self.x_vars[j][t][m], self.sm_vars[j][m]])
                        self.stats['running_clauses'] += 1

                        self.cnf.append([-self.x_vars[j][t][m]] + valid_starts)
                        self.stats['running_clauses'] += 1

                        for start_var in valid_starts:
                            self.cnf.append([-self.sm_vars[j][m], -start_var, self.x_vars[j][t][m]])
                            self.stats['running_clauses'] += 1
                    else:
                        self.cnf.append([-self.x_vars[j][t][m]])
                        self.stats['running_clauses'] += 1

    def add_resource_constraints(self):
        """Resource constraints"""
        # Renewable resources
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

                if resource_vars:
                    pb_constraint = PBEnc.atmost(resource_vars, resource_weights,
                                                 self.R_capacity[k], vpool=self.vpool)
                    self.cnf.extend(pb_constraint)
                    # Fix: Access clauses from CNFPlus object
                    self.stats['resource_clauses'] += len(pb_constraint.clauses)

        # Non-renewable resources
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
                # Fix: Access clauses from CNFPlus object
                self.stats['resource_clauses'] += len(pb_constraint.clauses)

    def encode(self):
        """Encode the complete problem"""
        print("\nEncoding with BASIC method...")

        # Create all variables
        print("  Creating variables...")
        self.create_variables()

        # Add all constraints
        print("  Adding start time constraints...")
        self.add_start_time_constraints()

        print("  Adding mode selection constraints...")
        self.add_mode_selection_constraints()

        print("  Adding precedence constraints...")
        self.add_precedence_constraints()

        print("  Adding running variable constraints...")
        self.add_running_variable_constraints()

        print("  Adding resource constraints...")
        self.add_resource_constraints()

        # Update totals
        self.stats['total_vars'] = self.vpool.top if hasattr(self.vpool, 'top') else self.vpool._top
        self.stats['total_clauses'] = len(self.cnf.clauses)

        print("  Encoding complete!")

        return self.cnf


def compare_encodings(instance_file):
    """Compare Basic and SCAMO encodings on a single instance"""

    print("=" * 100)
    print("COMPARISON OF ENCODING METHODS")
    print("=" * 100)

    # Read instance data
    print(f"\nReading instance: {instance_file}")
    reader = MRCPSPDataReader(instance_file)

    print(f"\nInstance Information:")
    print(f"  Number of jobs: {reader.data['num_jobs']}")
    print(f"  Horizon: {reader.get_horizon()}")
    print(f"  Renewable resources: {reader.data['num_renewable']} with capacity {reader.data['renewable_capacity']}")
    print(f"  Non-renewable resources: {reader.data['num_nonrenewable']} with capacity {reader.data['nonrenewable_capacity']}")

    # Count precedence relations
    total_precedences = sum(len(succs) for succs in reader.data['precedence'].values())
    print(f"  Total precedence relations: {total_precedences}")

    print("\n" + "=" * 100)

    # 1. BASIC ENCODING
    print("\n1. BASIC ENCODING (Traditional Approach)")
    print("-" * 60)

    start_time = time.time()
    basic_encoder = BasicEncoder(reader)
    basic_encoder.encode()
    basic_time = time.time() - start_time

    print(f"\nBasic Encoding Statistics:")
    print(f"  Total Variables: {basic_encoder.stats['total_vars']:,}")
    print(f"    - Start time variables: {basic_encoder.stats['start_time_vars']:,}")
    print(f"    - Mode variables: {basic_encoder.stats['mode_vars']:,}")
    print(f"    - Running variables: {basic_encoder.stats['running_vars']:,}")

    print(f"\n  Total Clauses: {basic_encoder.stats['total_clauses']:,}")
    print(f"    - Start time clauses: {basic_encoder.stats['start_time_clauses']:,}")
    print(f"    - Mode selection clauses: {basic_encoder.stats['mode_clauses']:,}")
    print(f"    - Precedence clauses: {basic_encoder.stats['precedence_clauses']:,}")
    print(f"    - Running variable clauses: {basic_encoder.stats['running_clauses']:,}")
    print(f"    - Resource clauses: {basic_encoder.stats['resource_clauses']:,}")

    print(f"\n  Encoding time: {basic_time:.3f} seconds")

    # 2. SCAMO BLOCK-BASED ENCODING
    print("\n" + "=" * 100)
    print("\n2. SCAMO BLOCK-BASED ENCODING")
    print("-" * 60)

    start_time = time.time()
    scamo_encoder = MRCPSPBlockBasedStaircase(reader)
    # Chỉ encode, không solve
    scamo_encoder.create_variables()
    scamo_encoder.add_start_time_constraints()
    scamo_encoder.add_mode_selection_constraints()
    scamo_encoder.add_precedence_constraints_with_blocks()
    scamo_encoder.add_process_variable_constraints()
    scamo_encoder.add_renewable_resource_constraints()
    scamo_encoder.add_nonrenewable_resource_constraints()
    scamo_encoder.stats['clauses'] = len(scamo_encoder.cnf.clauses)
    scamo_time = time.time() - start_time

    scamo_total_vars = scamo_encoder.vpool.top if hasattr(scamo_encoder.vpool, 'top') else scamo_encoder.vpool._top

    print(f"\nSCAMO Encoding Statistics:")
    print(f"  Total Variables: {scamo_total_vars:,}")
    print(f"    - Basic variables: {scamo_encoder.stats['variables']:,}")
    print(f"    - Register bits: {scamo_encoder.stats['register_bits']:,}")

    print(f"\n  Total Clauses: {scamo_encoder.stats['clauses']:,}")
    print(f"    - Connection clauses: {scamo_encoder.stats['connection_clauses']:,}")
    print(f"    - Precedence pairs encoded: {len(scamo_encoder.precedence_widths)}")

    print(f"\n  Encoding time: {scamo_time:.3f} seconds")

    # 3. COMPARISON SUMMARY
    print("\n" + "=" * 100)
    print("COMPARISON SUMMARY")
    print("=" * 100)

    print(f"\n{'Metric':<25} {'Basic':<20} {'SCAMO':<20} {'Difference':<20}")
    print("-" * 85)

    # Variables comparison
    var_diff = scamo_total_vars - basic_encoder.stats['total_vars']
    var_pct = (var_diff / basic_encoder.stats['total_vars']) * 100
    print(f"{'Total Variables':<25} {basic_encoder.stats['total_vars']:>19,} {scamo_total_vars:>19,} "
          f"{var_diff:>+10,} ({var_pct:+6.1f}%)")

    # Clauses comparison
    clause_diff = scamo_encoder.stats['clauses'] - basic_encoder.stats['total_clauses']
    clause_pct = (clause_diff / basic_encoder.stats['total_clauses']) * 100
    print(f"{'Total Clauses':<25} {basic_encoder.stats['total_clauses']:>19,} {scamo_encoder.stats['clauses']:>19,} "
          f"{clause_diff:>+10,} ({clause_pct:+6.1f}%)")

    # Time comparison
    time_diff = scamo_time - basic_time
    time_pct = (time_diff / basic_time) * 100 if basic_time > 0 else 0
    print(f"{'Encoding Time (s)':<25} {basic_time:>19.3f} {scamo_time:>19.3f} "
          f"{time_diff:>+10.3f} ({time_pct:+6.1f}%)")

def main():
    """Main function"""

    # Get instance file from command line or use default
    if len(sys.argv) > 1:
        instance_file = sys.argv[1]
    else:
        instance_file = "data/j10/j1018_8.mm"

    # Run comparison
    try:
        compare_encodings(instance_file)
    except FileNotFoundError:
        print(f"Error: File '{instance_file}' not found!")
        print(f"Usage: python {sys.argv[0]} <instance_file>")
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()