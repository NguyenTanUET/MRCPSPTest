import os, subprocess, tempfile, re
from pysat.formula import CNF

SAVILEROW_JAR = os.environ.get("SAVILEROW_JAR", "/home/you/savilerow/savilerow.jar")

EPRIME_TMPL = """\
language ESSENCE' 1.0

letting N be {N}
letting W be [ {weights} ]          $ trọng số 1..N
letting B be {bound}                $ ngưỡng

find X : matrix indexed by [int(1..N)] of bool

such that
  ( sum i : int(1..N) . W[i] * toInt(X[i]) ) <= B
"""

def compile_atmost(weights, bound, workdir=None):
    """
    Dùng Savile Row sinh CNF cho: sum_i weights[i]*X[i] <= bound
    Trả về: (cnf: pysat.CNF, x_var_ids: list[int] theo thứ tự X[1],X[2],...)
    """
    assert len(weights) > 0
    if workdir is None:
        workdir = tempfile.mkdtemp(prefix="srpb_")

    eprime_path = os.path.join(workdir, "pb.eprime")
    dimacs_path = os.path.join(workdir, "pb.dimacs")
    aux_path    = os.path.join(workdir, "pb.aux")

    # 1) tạo eprime nhúng dữ liệu (không dùng .param)
    with open(eprime_path, "w") as f:
        f.write(EPRIME_TMPL.format(
            N=len(weights),
            weights=', '.join(str(int(w)) for w in weights),
            bound=int(bound)
        ))

    # 2) gọi SR -> DIMACS + AUX
    cmd = [
        "java", "-Xmx2G", "-jar", SAVILEROW_JAR,
        "-in-eprime", eprime_path,
        "-out-sat", dimacs_path,
        "-out-aux", aux_path,
        "-sat", "minisat"
    ]
    subprocess.check_call(cmd, cwd=workdir)

    # 3) đọc CNF
    cnf = CNF(from_file=dimacs_path)

    # 4) lấy id SAT của X[i] theo thứ tự i=1..N
    #    Không parse varmap chi tiết: chỉ regex tên 'X_' trong .aux
    #    Savile Row thường có dòng: 'X_00001 is SAT variable 42' (hoặc tương tự)
    x_var_ids = [None]*len(weights)
    with open(aux_path, "r", errors="ignore") as f:
        for line in f:
            # khớp 'X_00007 ... SAT variable <id>'
            m = re.search(r'X_(\d+).*?SAT variable\s+(\d+)', line)
            if m:
                idx = int(m.group(1))  # 1-based
                vid = int(m.group(2))
                if 1 <= idx <= len(weights):
                    x_var_ids[idx-1] = vid

    # Trong trường hợp build khác, thử pattern dạng 'X[7]'
    if any(v is None for v in x_var_ids):
        with open(aux_path, "r", errors="ignore") as f:
            for line in f:
                m = re.search(r'X\[(\d+)\].*?SAT variable\s+(\d+)', line)
                if m:
                    idx = int(m.group(1))
                    vid = int(m.group(2))
                    if 1 <= idx <= len(weights):
                        x_var_ids[idx-1] = vid

    # fallback thô (hiếm khi cần): nếu vẫn thiếu, ném lỗi
    if any(v is None for v in x_var_ids):
        miss = [i+1 for i,v in enumerate(x_var_ids) if v is None]
        raise RuntimeError(f"Cannot map X indices from AUX, missing {miss}")

    return cnf, x_var_ids


def link_vars(target_cnf, x_ids, user_lits):
    """
    Nối X[i] ↔ user_lits[i] bằng 2 mệnh đề: (¬X ∨ L) ∧ (X ∨ ¬L)
    - x_ids: SAT var id (dương) từ SR
    - user_lits: literal của bạn (dương cho var, âm cho phủ định).
      Thường bạn truyền var id dương và để mình tạo tương đương với biến dương.
    """
    assert len(x_ids) == len(user_lits)
    for x, L in zip(x_ids, user_lits):
        # ép L về biến dương (nếu bạn muốn bắt X[i] ≡ (L>0))
        v = abs(int(L))
        # X -> v
        target_cnf.append([-x, v])
        # v -> X
        target_cnf.append([-v, x])