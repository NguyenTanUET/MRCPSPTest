"""
MRCPSP Block-Based Staircase Encoding
"""

from pysat.pb import PBEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose42
import time

class MRCPSPBlockBasedStaircase:
    """MRCPSP Encoder sử dụng Block-based Staircase technique từ PDF"""

    def __init__(self, mm_reader, block_width=10):
        self.cnf = CNF()
        self.vpool = IDPool()

        # Block configuration
        self.block_width = block_width  # w trong PDF

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
        Encode AMO block theo 4 công thức trong PDF
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
