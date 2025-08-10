"""
MRCPSP Register Formulas
Điều chỉnh công thức AMO/AMZ register từ RCPSP cho MRCPSP
"""


class MRCPSPRegisterEncoding:
    """
    Công thức register cho MRCPSP dựa trên ý tưởng AMO/AMZ của RCPSP
    """

    def __init__(self):
        pass

    def explain_register_formulas(self):
        """
        Giải thích các công thức register cho MRCPSP
        """
        print("=" * 80)
        print("CÔNG THỨC REGISTER CHO MRCPSP")
        print("=" * 80)

        print("\n1. ĐỊNH NGHĨA REGISTER:")
        print("   R_{i,j} = true ⟺ Job i đã bắt đầu trong khoảng [ES(i), j)")
        print("   Với: s_{i,t} = biến start time của job i tại thời điểm t")

        print("\n2. CÔNG THỨC ENCODING (dựa trên AMO/AMZ):")

        print("\n   (1) Forward implication:")
        print("       ⋁_{t=ES(i)}^{j-1} s_{i,t} → R_{i,j}")
        print("       Nếu job i bắt đầu tại bất kỳ t < j, thì R_{i,j} = true")

        print("\n   (2) Backward implication (mỗi variable riêng):")
        print("       ⋀_{t=ES(i)}^{j-1} (s_{i,t} → R_{i,j})")
        print("       Nếu job i bắt đầu tại t < j, thì R_{i,j} = true")

        print("\n   (3) Incremental definition:")
        print("       ¬s_{i,j} ∧ ¬R_{i,j} → ¬R_{i,j+1}")
        print("       Nếu job i chưa bắt đầu đến j VÀ không bắt đầu tại j")
        print("       thì cũng chưa bắt đầu đến j+1")

        print("\n   (4) Mutual exclusion:")
        print("       s_{i,j} → ¬R_{i,j}")
        print("       Nếu job i bắt đầu đúng tại j, thì chưa bắt đầu trước j")

    def encode_register_constraints(self, job, start_time, end_time):
        """
        Tạo các constraints để define register R_{job,[start,end)}

        Returns: list of clauses
        """
        clauses = []

        # Giả sử ta có:
        # - s_vars[job][t]: biến start time
        # - reg_var: biến register R_{job,end}

        # (1) Forward implication: OR(s_vars) → reg
        # Tương đương: ¬reg ∨ OR(s_vars)
        # Tương đương: ¬reg ∨ s[start] ∨ s[start+1] ∨ ... ∨ s[end-1]
        forward_clause = [-reg_var]
        for t in range(start_time, end_time):
            forward_clause.append(s_vars[job][t])
        clauses.append(forward_clause)

        # (2) Backward implication: mỗi s[t] → reg
        for t in range(start_time, end_time):
            clauses.append([-s_vars[job][t], reg_var])

        # (3) & (4) có thể thêm nếu cần incremental construction

        return clauses

    def compare_with_rcpsp(self):
        """
        So sánh với công thức RCPSP gốc
        """
        print("\n" + "=" * 80)
        print("SO SÁNH VỚI RCPSP")
        print("=" * 80)

        print("\nRCSPSP (AMO blocks):")
        print("- R_{i,j} track tổng số biến true trong block")
        print("- Dùng cho exactly-one constraint")

        print("\nMRCPSP (Staircase registers):")
        print("- R_{i,j} track 'đã bắt đầu chưa'")
        print("- Dùng cho precedence constraints")
        print("- Không cần track tổng số chính xác")

    def example_usage_in_precedence(self):
        """
        Ví dụ sử dụng register trong precedence constraint
        """
        print("\n" + "=" * 80)
        print("VÍ DỤ SỬ DỤNG TRONG PRECEDENCE")
        print("=" * 80)

        print("\nGiả sử: Job 1 → Job 2")
        print("Job 1 có mode với duration = 5")
        print("Nếu Job 1 kết thúc sau thời điểm k = 10")
        print("thì Job 2 không thể bắt đầu trước k = 10")

        print("\nStandard encoding:")
        print("Phải tạo nhiều clauses cho mỗi combination (t1, t2):")
        print("- ¬(sm[1][mode] ∧ s[1][6] ∧ s[2][0])")
        print("- ¬(sm[1][mode] ∧ s[1][6] ∧ s[2][1])")
        print("- ... (nhiều clauses)")

        print("\nStaircase với register:")
        print("Tạo R[2,10] = 'Job 2 bắt đầu trước t=10'")
        print("Chỉ cần ít clauses hơn:")
        print("- ¬(sm[1][mode] ∧ s[1][6] ∧ R[2,10])")
        print("- ¬(sm[1][mode] ∧ s[1][7] ∧ R[2,10])")
        print("- ... (ít hơn nhiều)")


def demonstrate_register_adaptation():
    """
    Demo cách điều chỉnh công thức register cho MRCPSP
    """
    encoder = MRCPSPRegisterEncoding()

    # Giải thích công thức
    encoder.explain_register_formulas()

    # So sánh với RCPSP
    encoder.compare_with_rcpsp()

    # Ví dụ usage
    encoder.example_usage_in_precedence()

    print("\n" + "=" * 80)
    print("TÓM TẮT ĐIỀU CHỈNH")
    print("=" * 80)

    print("\n1. THAY ĐỔI Ý NGHĨA:")
    print("   - RCPSP: R_{i,j} = 'exactly j variables true'")
    print("   - MRCPSP: R_{i,j} = 'job i started before j'")

    print("\n2. CÔNG THỨC ĐƠN GIẢN HƠN:")
    print("   - Không cần track chính xác số lượng")
    print("   - Chỉ cần biết đã bắt đầu hay chưa")

    print("\n3. HIỆU QUẢ:")
    print("   - Giảm số precedence clauses đáng kể")
    print("   - Trade-off: thêm register variables & definition clauses")

    print("\n4. KHI NÀO DÙNG:")
    print("   - Time windows lớn")
    print("   - Nhiều precedence constraints")
    print("   - Instance phức tạp")


# Pseudocode cho implementation thực tế
def create_staircase_register_implementation():
    """
    Pseudocode cho implementation thực tế trong solver
    """
    print("\n" + "=" * 80)
    print("PSEUDOCODE IMPLEMENTATION")
    print("=" * 80)

    code = '''
class StaircaseRegister:
    def __init__(self, solver):
        self.solver = solver
        self.register_cache = {}

    def get_or_create_register(self, job, start, end):
        """Get or create register for job starting in [start, end)"""
        key = (job, start, end)

        if key in self.register_cache:
            return self.register_cache[key]

        # Create new register variable
        reg_var = self.solver.new_var(f"R_{job}_{start}_{end}")

        # Add definition constraints
        # (1) OR(s[job][t] for t in [start,end)) → reg
        or_clause = [-reg_var]
        for t in range(start, end):
            if self.has_start_var(job, t):
                or_clause.append(self.s_vars[job][t])
        self.solver.add_clause(or_clause)

        # (2) Each s[job][t] → reg
        for t in range(start, end):
            if self.has_start_var(job, t):
                self.solver.add_clause([-self.s_vars[job][t], reg_var])

        self.register_cache[key] = reg_var
        return reg_var

    def encode_precedence_with_register(self, pred, succ):
        """Encode precedence pred → succ using registers"""
        for k in range(ES[succ], LS[succ] + 1):
            # Get register: succ starts before k
            reg_succ = self.get_or_create_register(succ, ES[succ], k)

            for mode in modes[pred]:
                duration = durations[pred][mode]

                # If pred finishes after k, succ cannot start before k
                for t_pred in range(k - duration + 1, LS[pred] + 1):
                    if t_pred >= ES[pred]:
                        self.solver.add_clause([
                            -self.sm_vars[pred][mode],
                            -self.s_vars[pred][t_pred],
                            -reg_succ
                        ])
    '''

    print(code)


if __name__ == "__main__":
    # Demo các công thức
    demonstrate_register_adaptation()

    # Pseudocode implementation
    create_staircase_register_implementation()