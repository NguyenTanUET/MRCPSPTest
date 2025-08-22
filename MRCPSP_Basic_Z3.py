# MRCPSP_SMT_Z3_pretty.py
# -----------------------------------------------------------
# Giải 1 instance MMLIB50 bằng Z3 (SMT), in kết quả & validate.
# In thêm: tổng số ràng buộc (assertions), tổng số biến quyết định, thời gian giải.
# -----------------------------------------------------------

from pathlib import Path
from typing import Dict, List, Tuple
import time
from docplex.cp import utils_visu as visu

from z3 import Int, If, And, Or, Sum, Optimize, sat
from MRCPSP_Basic import MRCPSPDataReader  # <-- dùng reader sẵn có của bạn


def _build_renewable_segments(schedule, reqR, R, horizon):
    """Trả về list[res] -> segments [(s,e,val), ...] biểu diễn tải tài nguyên theo thời gian"""
    segs_all = []
    for k in range(R):
        # usage theo mỗi slot [t, t+1)
        usage = [0]*(horizon)
        for (j, mj, sj, dj, fj, _rvec) in schedule:
            req = reqR[j][mj][k]  # nhu cầu resource k của job j ở mode mj
            if req == 0:
                continue
            for t in range(sj, min(fj, horizon)):
                usage[t] += req
        # nén thành segments
        segs = []
        cur_val = usage[0] if horizon > 0 else 0
        cur_start = 0
        for t in range(1, horizon):
            if usage[t] != cur_val:
                segs.append((cur_start, t, cur_val))
                cur_start = t
                cur_val = usage[t]
        if horizon > 0:
            segs.append((cur_start, horizon, cur_val))
        segs_all.append(segs)
    return segs_all

def visualize_with_visu(mm_path, schedule, ms, R, N, R_cap, reqR):

    # Timeline tiêu đề
    from pathlib import Path
    filename = Path(mm_path).name
    visu.timeline('Solution for RCPSPMM ' + filename)

    # Panel công việc
    visu.panel('Tasks')
    for (j, mj, sj, dj, fj, rvec) in schedule:
        # color: dùng chỉ số job cho dễ phân biệt; name có mode
        visu.interval(sj, fj, int(j), f"J{j}  m{mj+1}")

    # Các panel tài nguyên tái tạo
    if R > 0:
        INTERVAL_MIN, INTERVAL_MAX = 0, ms
        load_segments = _build_renewable_segments(schedule, reqR, R, ms)
        for j in range(R):
            visu.panel('R ' + str(j + 1))
            # nền công suất (màu xám nhạt) và đồ thị tải (màu index j)
            visu.function(segments=[(INTERVAL_MIN, INTERVAL_MAX, R_cap[j])], style='area', color='lightgrey')
            visu.function(segments=load_segments[j], style='area', color=j)

    visu.show()


# =========================
# Đọc & chuẩn hóa dữ liệu
# =========================
def build_instance(reader: MRCPSPDataReader):
    dat = reader.data
    J = dat['num_jobs']                          # gồm cả 1 (source) và J (sink)
    R = dat.get('num_renewable', 0)
    N = dat.get('num_nonrenewable', 0)
    R_cap = dat.get('renewable_capacity', [0]*R)
    N_cap = dat.get('nonrenewable_capacity', [0]*N)
    prec: Dict[int, List[int]] = dat.get('precedence', {})
    modes: Dict[int, List[Tuple[int, List[int]]]] = dat.get('job_modes', {})
    H = reader.get_horizon()

    # duration theo mode; reqR/reqN tách theo R và N
    dur = {j: [m[0] for m in modes.get(j, [])] for j in range(1, J+1)}
    reqR = {j: [[m[1][k] if k < R else 0 for k in range(R)] for m in modes.get(j, [])] for j in range(1, J+1)}
    reqN = {j: [[m[1][R+k] if (R+k) < len(m[1]) else 0 for k in range(N)] for m in modes.get(j, [])] for j in range(1, J+1)}

    # Bảo đảm job nào cũng có ít nhất 1 mode
    for j in range(1, J+1):
        if len(dur[j]) == 0:
            dur[j] = [0]
            reqR[j] = [[0]*R]
            reqN[j] = [[0]*N]

    return J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H

# =========================
# Encode SMT + Giải
# =========================
def solve_mrcpsp_with_z3(mm_path: str, timeout_ms: int = 600_000):
    reader = MRCPSPDataReader(mm_path)
    J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H = build_instance(reader)

    opt = Optimize()
    if timeout_ms is not None:
        opt.set(timeout=timeout_ms)

    # Biến quyết định
    mode = {}   # mode[j] ∈ [0..#modes_j-1]
    s = {}      # s[j] ∈ [0..H]
    for j in range(1, J+1):
        mode[j] = Int(f"mode_{j}")
        s[j]    = Int(f"s_{j}")
        opt.add(And(mode[j] >= 0, mode[j] < len(dur[j])))
        opt.add(And(s[j] >= 0, s[j] <= H))
    M = Int("M")
    opt.add(M >= 0)

    # Helper theo mode chọn
    def dur_of(j):
        return Sum([If(mode[j] == m, dur[j][m], 0) for m in range(len(dur[j]))])

    def reqR_of(j, k):
        return Sum([If(mode[j] == m, reqR[j][m][k], 0) for m in range(len(reqR[j]))]) if R > 0 else 0

    def reqN_of(j, k):
        return Sum([If(mode[j] == m, reqN[j][m][k], 0) for m in range(len(reqN[j]))]) if N > 0 else 0

    # 1) Precedence
    for i in range(1, J+1):
        for j in prec.get(i, []):
            opt.add(s[j] >= s[i] + dur_of(i))

    # 2) Renewable per time
    for k in range(R):
        for t in range(H+1):
            usage_terms = []
            for j in range(1, J+1):
                dj = dur_of(j)
                active = If(And(s[j] <= t, t < s[j] + dj), 1, 0)
                usage_terms.append(reqR_of(j, k) * active)
            opt.add(Sum(usage_terms) <= R_cap[k])

    # 3) Non-renewable (global)
    for k in range(N):
        opt.add(Sum([reqN_of(j, k) for j in range(1, J+1)]) <= N_cap[k])

    # 4) Makespan & minimize
    for j in range(1, J+1):
        opt.add(M >= s[j] + dur_of(j))
    opt.minimize(M)

    # Đếm ràng buộc & biến (cho báo cáo)
    # - ràng buộc = số assertions hiện có trong Optimize
    # - biến = (#mode + #s + 1*M)
    num_constraints = len(opt.assertions())
    num_variables   = (len(mode) + len(s) + 1)

    # Giải
    t0 = time.time()
    res = opt.check()
    solve_time = time.time() - t0

    if res != sat:
        print("✗ UNSAT/UNKNOWN")
        print(f"Tổng ràng buộc (assertions): {num_constraints}")
        print(f"Tổng biến quyết định    : {num_variables}")
        print(f"Tổng thời gian giải      : {solve_time:.2f}s")
        return None

    m = opt.model()
    ms = m[M].as_long()

    # Dịch nghiệm
    schedule = []
    for j in range(1, J+1):
        mj = m[mode[j]].as_long()
        sj = m[s[j]].as_long()
        dj = dur[j][mj]
        fj = sj + dj
        # vector tài nguyên theo mode (R trước rồi N)
        res_vec = []
        if R > 0:
            res_vec += [reqR[j][mj][k] for k in range(R)]
        if N > 0:
            res_vec += [reqN[j][mj][k] for k in range(N)]
        schedule.append((j, mj, sj, dj, fj, res_vec))
    schedule.sort(key=lambda x: (x[2], x[0]))

    # In giống mẫu
    print("=== SOLUTION ===")
    print(f"Makespan: {ms}\n")
    # Header bảng
    # Tạo nhãn resources như ví dụ (giả sử 2R+2N -> 4 cột). Tổng cột = R+N.
    res_header_items = []
    for k in range(R):
        res_header_items.append(f"R{k+1}")
    for k in range(N):
        res_header_items.append(f"N{k+1}")
    res_header = "  ".join([f"{h:>2s}" for h in res_header_items]) if (R+N) > 0 else ""
    print("Job   Mode   Start   Duration   Finish   " + ("Resources" if res_header == "" else f"Resources ({' '.join(res_header_items)})"))
    print("-"*65)

    for (j, mj, sj, dj, fj, rvec) in schedule:
        # in resources: căn lề dạng số 2 chữ rộng như ví dụ
        if len(rvec) > 0:
            rstr = "  ".join([f"{x:>2d}" for x in rvec])
            print(f"{j:<5d}{(mj+1):<7d}{sj:<8d}{dj:<11d}{fj:<9d} {rstr:<}")
        else:
            print(f"{j:<5d}{(mj+1):<7d}{sj:<8d}{dj:<11d}{fj:<9d}")

    # ===== VALIDATION =====
    print("\n=== VALIDATING SOLUTION ===")
    # Actual makespan
    actual_ms = max(fj for *_, fj, _ in [(j, mj, sj, dj, fj, rv) for (j,mj,sj,dj,fj,rv) in schedule])
    print(f"Actual makespan from solution: {actual_ms}\n")

    ok_prec = True
    print("Checking precedence constraints...")
    for i in range(1, J+1):
        for j2 in reader.data.get('precedence', {}).get(i, []):
            # lấy (s_i, dur_i chosen)
            si = next(x[2] for x in schedule if x[0] == i)
            mi = next(x[1] for x in schedule if x[0] == i)
            di = dur[i][mi]
            sj2 = next(x[2] for x in schedule if x[0] == j2)
            if sj2 < si + di:
                ok_prec = False
                break
        if not ok_prec: break
    print("  ✓ All precedence constraints satisfied" if ok_prec else "  ✗ Violation found")

    ok_R = True
    if reader.data.get('num_renewable', 0) > 0:
        print("\nChecking renewable resource constraints...")
        for t in range(ms+1):
            for k in range(R):
                usage = 0
                for (j,mj,sj,dj,fj,_) in schedule:
                    if sj <= t < fj:
                        usage += reqR[j][mj][k]
                if usage > R_cap[k]:
                    ok_R = False
                    break
            if not ok_R: break
        print("  ✓ All renewable resource constraints satisfied" if ok_R else "  ✗ Violation found")
    else:
        print("\n(No renewable resources)")

    ok_N = True
    if reader.data.get('num_nonrenewable', 0) > 0:
        print("\nChecking non-renewable resource constraints...")
        for k in range(N):
            total = sum(reqN[j][m][k] for (j,m,_,_,_,_) in schedule)
            if total > N_cap[k]:
                ok_N = False
                break
        print("  ✓ All non-renewable resource constraints satisfied" if ok_N else "  ✗ Violation found")
    else:
        print("\n(No non-renewable resources)")

    all_ok = ok_prec and ok_R and ok_N and (actual_ms == ms)
    if all_ok:
        print("\n✓ Solution is VALID!\n")
    else:
        print("\n✗ Solution is NOT valid.\n")

    print(f"✓ Successfully found optimal makespan = {ms}")
    print(f"Tổng ràng buộc (assertions): {num_constraints}")
    print(f"Tổng biến quyết định    : {num_variables}")
    print(f"Total solving time: {solve_time:.2f}s")

    visualize_with_visu(mm_path, schedule, ms, R, N, R_cap, reqR)

    return {
        "makespan": ms,
        "solve_time": solve_time,
        "num_constraints": num_constraints,
        "num_variables": num_variables,
        "schedule": schedule,
    }

# =========================
# Run: Ấn Run là chạy 1 file
# =========================
if __name__ == "__main__":
    DEFAULT_INSTANCE = "data/j20/j2010_3.mm"  # sửa sang file bạn muốn

    print("="*100)
    print("RUN ONE J20 INSTANCE (Z3 SMT) — Pretty Output")
    print("="*100)
    print(f"Instance: {DEFAULT_INSTANCE}\n")
    solve_mrcpsp_with_z3(DEFAULT_INSTANCE, timeout_ms=600_000)
