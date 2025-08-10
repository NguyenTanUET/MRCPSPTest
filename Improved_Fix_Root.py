"""
MRCPSP Block-Based Staircase Encoding
Implement theo phương pháp trong PDF với chia blocks, AMO/AMZ blocks và ghép blocks
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
from Adaptive import AdaptiveBlockWidth
import time


class MRCPSPBlockBasedStaircase:
    """MRCPSP Encoder sử dụng Block-based Staircase technique từ PDF"""

    def __init__(self, mm_reader, block_width=None, use_adaptive=True):
        self.cnf = CNF()
        self.vpool = IDPool()

        # Block configuration
        if use_adaptive:
            adaptive = AdaptiveBlockWidth(mm_reader)
            if block_width == 'per-job':
                # Mỗi job có width riêng
                self.job_widths = adaptive.get_adaptive_widths_all_jobs()
            else:
                # Một width chung cho cả instance
                self.block_width = adaptive.get_global_adaptive_width()
        else:
            self.block_width = block_width or 10

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
        self.blocks = {}  # {job: [(block_id, start, end, type)]}
        self.register_bits = {}  # Register bits cho mỗi block
        self.block_connections = []  # Danh sách connections giữa blocks

        # Statistics
        self.stats = {
            'variables': 0,
            'clauses': 0,
            'amo_blocks': 0,
            'amz_blocks': 0,
            'register_bits': 0,
            'connection_clauses': 0
        }

    def calculate_time_windows(self):
        """Tính ES và LS cho mỗi job"""
        self.ES = {}
        self.LS = {}

        for j in range(1, self.jobs + 1):
            self.ES[j] = 0
            self.LS[j] = self.horizon

        # Forward pass
        self.ES[1] = 0

        def calc_es(j):
            if j in self.ES and self.ES[j] > 0:
                return self.ES[j]

            max_pred_finish = 0
            for pred in range(1, self.jobs + 1):
                if pred in self.precedence and j in self.precedence[pred]:
                    pred_es = calc_es(pred)
                    min_duration = min(mode[0] for mode in self.job_modes[pred])
                    max_pred_finish = max(max_pred_finish, pred_es + min_duration)

            self.ES[j] = max_pred_finish
            return self.ES[j]

        for j in range(1, self.jobs + 1):
            calc_es(j)

        # Backward pass
        for j in range(1, self.jobs + 1):
            max_duration = max(mode[0] for mode in self.job_modes[j])
            self.LS[j] = min(self.LS[j], self.horizon - max_duration)

    def create_blocks_for_job(self, job):
        """
        Chia time window của job thành blocks theo block_width
        Giống Section 3.1 trong PDF
        """
        blocks = []
        time_window_start = self.ES[job]
        time_window_end = self.LS[job] + 1

        # Số blocks cần thiết
        num_blocks = (time_window_end - time_window_start + self.block_width - 1) // self.block_width

        block_id = 0
        for i in range(num_blocks):
            start = time_window_start + i * self.block_width
            end = min(start + self.block_width, time_window_end)

            if start < end:
                # Block đầu tiên luôn là AMO
                # Block cuối cùng luôn là AMO
                # Các block giữa: AMO và AMZ
                if i == 0 or i == num_blocks - 1:
                    blocks.append((block_id, start, end, 'AMO'))
                    block_id += 1
                else:
                    # Tạo cả AMO và AMZ blocks cho block giữa
                    blocks.append((block_id, start, end, 'AMO'))
                    block_id += 1
                    blocks.append((block_id, start, end, 'AMZ'))
                    block_id += 1

        self.blocks[job] = blocks
        return blocks

    def create_register_bits_for_block(self, job, block_id, start, end, block_type):
        """
        Tạo register bits cho một block
        Giống Section 3.1 trong PDF với R_{i,j}
        """
        block_vars = []
        register_bits = []

        # Tạo/lấy biến s_{j,t} cho block này
        for t in range(start, end):
            if t not in self.s_vars[job]:
                var = self.vpool.id(f's_{job}_{t}')
                self.s_vars[job][t] = var
                self.stats['variables'] += 1
            block_vars.append(self.s_vars[job][t])

        # Tạo register bits R_{block,j} cho j=1..len(block_vars)
        # R_{block,1} = x_1 (biến đầu tiên)
        if len(block_vars) > 0:
            register_bits.append(block_vars[0])

            # R_{block,j} cho j=2..len
            for j in range(2, len(block_vars) + 1):
                reg_var = self.vpool.id(f'R_{job}_{block_id}_{j}')
                register_bits.append(reg_var)
                self.stats['register_bits'] += 1

        self.register_bits[(job, block_id)] = register_bits
        return register_bits

    def encode_amo_block(self, job, block_id, start, end):
        """
        Encode AMO block theo 4 công thức trong PDF (Section 3.1)
        """
        block_vars = [self.s_vars[job][t] for t in range(start, end) if t in self.s_vars[job]]
        register_bits = self.register_bits[(job, block_id)]

        if len(block_vars) <= 1:
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

        # Formula (4): x_{i,j} → ¬R_{i,j-1}
        for j in range(1, len(block_vars)):
            self.cnf.append([-block_vars[j], -register_bits[j - 1]])
            self.stats['clauses'] += 1

        self.stats['amo_blocks'] += 1

    def encode_amz_block(self, job, block_id, start, end):
        """
        Encode AMZ block - giống AMO nhưng không có formula (4)
        """
        block_vars = [self.s_vars[job][t] for t in range(start, end) if t in self.s_vars[job]]
        register_bits = self.register_bits[(job, block_id)]

        if len(block_vars) <= 1:
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

        # KHÔNG có formula (4) cho AMZ

        self.stats['amz_blocks'] += 1

    def connect_blocks(self, job, block1_info, block2_info):
        """
        Kết nối 2 blocks liên tiếp
        Implement connection như Section 3.1 cuối trong PDF
        """
        block1_id, start1, end1, type1 = block1_info
        block2_id, start2, end2, type2 = block2_info

        # Chỉ connect AMO blocks
        if type1 != 'AMO' or type2 != 'AMO':
            return

        # Lấy register bits
        reg_bits1 = self.register_bits.get((job, block1_id), [])
        reg_bits2 = self.register_bits.get((job, block2_id), [])

        if not reg_bits1 or not reg_bits2:
            return

        # Số connections = min(len(reg_bits1), len(reg_bits2)) - 1
        num_connections = min(len(reg_bits1), len(reg_bits2)) - 1

        for j in range(1, num_connections + 1):
            # ¬R_{block1,j} ∨ ¬R_{block2,j}
            if j < len(reg_bits1) and j < len(reg_bits2):
                self.cnf.append([-reg_bits1[j], -reg_bits2[j]])
                self.stats['connection_clauses'] += 1

        self.block_connections.append((job, block1_id, block2_id))

    def create_variables(self):
        """Tạo các biến cơ bản"""
        # s_{j,t} variables
        self.s_vars = {}
        for j in range(1, self.jobs + 1):
            self.s_vars[j] = {}

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
                    earliest = max(0, t - duration + 1)
                    latest = t

                    if earliest <= self.LS[j] and latest >= self.ES[j]:
                        var = self.vpool.id(f'u_{j}_{t}_{m}')
                        self.u_vars[j][t][m] = var
                        self.stats['variables'] += 1

    def encode_job_with_blocks(self, job):
        """Encode một job sử dụng block structure"""
        # 1. Tạo blocks cho job
        blocks = self.create_blocks_for_job(job)

        # 2. Tạo register bits và encode từng block
        for block_id, start, end, block_type in blocks:
            # Tạo register bits
            self.create_register_bits_for_block(job, block_id, start, end, block_type)

            # Encode block
            if block_type == 'AMO':
                self.encode_amo_block(job, block_id, start, end)
            else:  # AMZ
                self.encode_amz_block(job, block_id, start, end)

        # 3. Connect consecutive AMO blocks
        amo_blocks = [b for b in blocks if b[3] == 'AMO']
        for i in range(len(amo_blocks) - 1):
            self.connect_blocks(job, amo_blocks[i], amo_blocks[i + 1])

    def add_start_time_constraints(self):
        """Exactly one start time cho mỗi job - sử dụng block structure"""
        for j in range(1, self.jobs + 1):
            # Encode job với blocks
            self.encode_job_with_blocks(j)

            # Thêm constraint: tổng tất cả blocks = 1
            # Điều này đảm bảo exactly one start time
            all_vars = []
            for t in range(self.ES[j], self.LS[j] + 1):
                if t in self.s_vars[j]:
                    all_vars.append(self.s_vars[j][t])

            if len(all_vars) > 0:
                # At least one
                self.cnf.append(all_vars)
                self.stats['clauses'] += 1

    def add_mode_selection_constraints(self):
        """Mode selection constraints"""
        for j in range(1, self.jobs + 1):
            mode_vars = [self.sm_vars[j][m] for m in range(len(self.job_modes[j]))]

            # Exactly one mode
            self.cnf.append(mode_vars)
            self.stats['clauses'] += 1

            for i in range(len(mode_vars)):
                for k in range(i + 1, len(mode_vars)):
                    self.cnf.append([-mode_vars[i], -mode_vars[k]])
                    self.stats['clauses'] += 1

    def add_precedence_constraints_with_blocks(self):
        """
        Precedence constraints sử dụng register bits từ blocks
        """
        for predecessor in range(1, self.jobs + 1):
            if predecessor not in self.precedence:
                continue

            for successor in self.precedence[predecessor]:
                # Sử dụng register bits để encode precedence hiệu quả hơn
                self._encode_precedence_using_blocks(predecessor, successor)

    def _encode_precedence_using_blocks(self, pred, succ):
        """Helper để encode precedence sử dụng block registers"""
        # Lấy blocks của successor
        succ_blocks = self.blocks.get(succ, [])

        for m_pred in range(len(self.job_modes[pred])):
            duration_pred = self.job_modes[pred][m_pred][0]

            # Với mỗi block của successor
            for block_id, start, end, block_type in succ_blocks:
                if block_type != 'AMO':
                    continue

                # Kiểm tra xem predecessor có thể vi phạm block này không
                for t in range(start, end):
                    latest_start_pred = t - duration_pred

                    if latest_start_pred >= self.ES[pred]:
                        # Sử dụng register bit thay vì enumerate từng variable
                        reg_bits = self.register_bits.get((succ, block_id), [])

                        # Tìm register bit phù hợp cho time t
                        reg_index = t - start
                        if reg_index < len(reg_bits):
                            # Nếu pred starts sau latest_start_pred với mode m_pred
                            # thì succ không thể start trước t
                            for t_pred in range(latest_start_pred + 1, self.LS[pred] + 1):
                                if t_pred in self.s_vars[pred]:
                                    self.cnf.append([
                                        -self.sm_vars[pred][m_pred],
                                        -self.s_vars[pred][t_pred],
                                        -reg_bits[reg_index]
                                    ])
                                    self.stats['clauses'] += 1

    def add_process_variable_constraints(self):
        """Define process variables từ start variables và modes"""
        for j in range(1, self.jobs + 1):
            for t in range(self.horizon + 1):
                for m in range(len(self.job_modes[j])):
                    if m not in self.u_vars[j][t]:
                        continue

                    duration = self.job_modes[j][m][0]

                    # u_{j,t,m} = true if job j runs at t with mode m
                    valid_starts = []
                    for t_start in range(max(self.ES[j], t - duration + 1),
                                         min(self.LS[j] + 1, t + 1)):
                        if t_start in self.s_vars[j] and t_start + duration > t:
                            valid_starts.append(self.s_vars[j][t_start])

                    if valid_starts:
                        # u => sm
                        self.cnf.append([-self.u_vars[j][t][m], self.sm_vars[j][m]])
                        self.stats['clauses'] += 1

                        # u => OR(valid_starts)
                        self.cnf.append([-self.u_vars[j][t][m]] + valid_starts)
                        self.stats['clauses'] += 1

                        # sm AND start => u
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
        """Encode complete problem với block-based approach"""
        print("Creating variables...")
        self.create_variables()

        print("Adding start time constraints with blocks...")
        self.add_start_time_constraints()

        print("Adding mode selection constraints...")
        self.add_mode_selection_constraints()

        print("Adding precedence constraints with blocks...")
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

        # Update stats
        self.stats['clauses'] = len(self.cnf.clauses)

        print(f"\nBlock-based encoding statistics:")
        print(f"  Total variables: {self.vpool.top}")
        print(f"  - Basic vars: {self.stats['variables']}")
        print(f"  - Register bits: {self.stats['register_bits']}")
        print(f"  Total clauses: {self.stats['clauses']}")
        print(f"  - AMO blocks: {self.stats['amo_blocks']}")
        print(f"  - AMZ blocks: {self.stats['amz_blocks']}")
        print(f"  - Connection clauses: {self.stats['connection_clauses']}")
        print(f"  Block width: {self.block_width}")

        return self.cnf

    def solve(self, makespan):
        """Solve với makespan cho trước"""
        print(f"\n--- Solving with makespan = {makespan} ---")

        # Reset
        self.cnf = CNF()
        self.vpool = IDPool()
        self.blocks = {}
        self.register_bits = {}
        self.block_connections = []
        self.stats = {
            'variables': 0,
            'clauses': 0,
            'amo_blocks': 0,
            'amz_blocks': 0,
            'register_bits': 0,
            'connection_clauses': 0
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
        """Extract solution"""
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

        print(f"Searching for optimal makespan in [{min_makespan}, {max_makespan}]")
        print(f"Using block width: {self.block_width}")

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

    def calculate_critical_path_bound(self):
        """Calculate critical path bound"""
        return self.ES[self.jobs] if self.jobs in self.ES else 1


def test_block_based_encoding():
    """Test và so sánh với encoding cũ"""

    # Import cần thiết
    import sys
    sys.path.append('.')

    try:
        from MRCPSTest import MRCPSPDataReader
    except:
        print("Cannot import MRCPSPDataReader")
        return

    # Test với các block widths khác nhau
    test_file = "data/j10/j1014_8.mm"
    block_widths = [5, 10, 15, 20]

    print("=" * 100)
    print("TESTING BLOCK-BASED STAIRCASE ENCODING")
    print("=" * 100)

    reader = MRCPSPDataReader(test_file)

    print(f"\nInstance: {test_file}")
    print(f"Jobs: {reader.data['num_jobs']}")
    print(f"Horizon: {reader.get_horizon()}")

    for width in block_widths:
        print(f"\n{'=' * 60}")
        print(f"Testing with block width = {width}")
        print('=' * 60)

        encoder = MRCPSPBlockBasedStaircase(reader, block_width=width)

        # Test với một makespan cụ thể
        test_makespan = reader.get_horizon() // 2
        solution = encoder.solve(test_makespan)

        if solution:
            print(f"Found solution with makespan {test_makespan}")
        else:
            print(f"No solution with makespan {test_makespan}")


if __name__ == "__main__":
    test_block_based_encoding()