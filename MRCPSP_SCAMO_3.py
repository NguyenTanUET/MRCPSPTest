"""
MRCPSP Block-Based Staircase Encoding với Precedence-Aware Adaptive Width
Độ rộng block phụ thuộc vào mối quan hệ precedence giữa các jobs
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
        self.calculate_time_windows()

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

        # Initialize
        for j in range(1, self.jobs + 1):
            self.ES[j] = 0
            self.LS[j] = self.horizon

        # Forward pass for ES
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
            print(f"  Average: {sum(widths)/len(widths):.1f}")
            print(f"  Min: {min(widths)}, Max: {max(widths)}")
            print(f"  Total precedence pairs: {len(self.precedence_widths)}")

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
        """Create (or reuse) register bits for a block"""
        if block_id in self.register_bits:
            return self.register_bits[block_id]

        block_vars = []
        register_bits = []
        for t in range(start, end):
            if t in self.s_vars[job]:
                block_vars.append(self.s_vars[job][t])
        if len(block_vars) > 0:
            register_bits.append(block_vars[0])
            for j in range(2, len(block_vars) + 1):
                rb = self.vpool.id(f'R_{block_id}_{j}')
                register_bits.append(rb)
                self.stats['register_bits'] += 1
        self.register_bits[block_id] = (register_bits, block_vars)
        return register_bits, block_vars

    def encode_amo_block(self, block_id, job, start, end):
        """Encode AMO block with 4 formulas (idempotent by block_id)"""
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

        for j in range(1, len(block_vars)):
            self.cnf.append([-register_bits[j - 1], register_bits[j]])
            self.stats['clauses'] += 1

        for j in range(1, len(block_vars)):
            self.cnf.append([block_vars[j], register_bits[j - 1], -register_bits[j]])
            self.stats['clauses'] += 1

        for j in range(1, len(block_vars)):
            self.cnf.append([-block_vars[j], -register_bits[j - 1]])
            self.stats['clauses'] += 1

        self.stats['amo_blocks'] += 1
        self.encoded_blocks.add(block_id)

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

        self.stats['amz_blocks'] += 1

    def connect_blocks(self, block1_id, block2_id):
        """Connect two consecutive AMO blocks (idempotent)"""
        if block1_id not in self.register_bits or block2_id not in self.register_bits:
            return

        pair = (block1_id, block2_id)
        if pair in self.connected_pairs:
            return
        self.connected_pairs.add(pair)

        reg_bits1, _ = self.register_bits[block1_id]
        reg_bits2, _ = self.register_bits[block2_id]
        if not reg_bits1 or not reg_bits2:
            return

        # Connection clauses
        num_connections = min(len(reg_bits1), len(reg_bits2)) - 1
        for j in range(1, num_connections + 1):
            if j < len(reg_bits1) and j < len(reg_bits2):
                self.cnf.append([-reg_bits1[j], -reg_bits2[j]])
                self.stats['connection_clauses'] += 1

    
    def add_start_time_constraints(self):
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
        """Exactly one mode for each job"""
        for j in range(1, self.jobs + 1):
            mode_vars = [self.sm_vars[j][m] for m in range(len(self.job_modes[j]))]

            # At least one mode
            self.cnf.append(mode_vars)
            self.stats['clauses'] += 1

            # At most one mode
            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    self.cnf.append([-mode_vars[i], -mode_vars[k]])
                    self.stats['clauses'] += 1

    
    def add_precedence_constraints_with_blocks(self):
        for pred in range(1, self.jobs + 1):
            if pred not in self.precedence:
                continue
            for succ in self.precedence[pred]:
                # Ensure succ blocks exist (built in start-time step)
                if succ not in self.job_blocks or not self.job_blocks[succ]:
                    blocks = self.create_blocks_for_job(succ)
                    for (bid, st, en, _bt, _a, _b) in blocks:
                        self.encode_amo_block(bid, succ, st, en)
                    for i in range(len(blocks) - 1):
                        self.connect_blocks(blocks[i][0], blocks[i + 1][0])

                blocks = self.job_blocks[succ]
                # Sort by start to identify 'fully-before' blocks
                blocks = sorted(blocks, key=lambda b: b[1])

                for m_pred in range(len(self.job_modes[pred])):
                    dur = self.job_modes[pred][m_pred][0]
                    for t_pred in range(self.ES[pred], self.LS[pred] + 1):
                        if t_pred not in self.s_vars[pred]:
                            continue
                        earliest = t_pred + dur
                        threshold = earliest - 1  # last forbidden time

                        # Skip if threshold before succ ES
                        if threshold < self.ES[succ]:
                            continue

                        # 1) For every block fully <= threshold: force last register bit = 0
                        for (bid, st, en, _bt, _a, _b) in blocks:
                            last_time = en - 1
                            if last_time <= threshold and st <= last_time:
                                # ensure the block has registers
                                reg_bits, block_vars = self.create_register_bits_for_block(bid, succ, st, en)
                                if block_vars:
                                    idx = len(block_vars) - 1
                                    rb = reg_bits[idx]
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -rb])
                                    self.stats['clauses'] += 1

                        # 2) For the block that contains threshold: force prefix up to (threshold) = 0
                        for (bid, st, en, _bt, _a, _b) in blocks:
                            if st <= threshold < en:
                                reg_bits, block_vars = self.create_register_bits_for_block(bid, succ, st, en)
                                if block_vars:
                                    idx = threshold - st
                                    rb = reg_bits[idx]
                                    self.cnf.append([-self.sm_vars[pred][m_pred], -self.s_vars[pred][t_pred], -rb])
                                    self.stats['clauses'] += 1
                                break  # only one containing block


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
        print(f"Total blocks: {self.stats['total_blocks']}")
        print(f"  - AMO blocks: {self.stats['amo_blocks']}")
        print(f"  - AMZ blocks: {self.stats['amz_blocks']}")
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
            print(f"{j:<5} {info['mode']+1:<6} {info['start_time']:<7} "
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
                    print(f"  ✗ Renewable resource {k+1} violated at time {t}: "
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
                print(f"  ✗ Non-renewable resource {k+1} violated: "
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
        test_file = "data/j10/j1042_9.mm"

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
