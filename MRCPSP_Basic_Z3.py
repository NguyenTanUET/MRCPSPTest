# MRCPSP_SMT_Z3_formulation.py
# Encode y nguyên theo formulation (3.1)–(3.7) dùng Bool x_{i,t,o}, sm_{i,o}

from pathlib import Path
from typing import Dict, List, Tuple
import time
from z3 import Bool, Int, If, And, Or, Sum, Optimize, Implies, sat

from MRCPSP_Basic import MRCPSPDataReader

# -------------------------
# Helpers
# -------------------------
def bool_sum(lits):  # Sum Bool -> Int
    return Sum([If(l, 1, 0) for l in lits])

def build_instance(reader: MRCPSPDataReader):
    dat = reader.data
    J = dat['num_jobs']                              # gồm cả source/sink
    R = dat.get('num_renewable', 0)
    N = dat.get('num_nonrenewable', 0)
    R_cap = dat.get('renewable_capacity', [0]*R)
    N_cap = dat.get('nonrenewable_capacity', [0]*N)
    prec: Dict[int, List[int]] = dat.get('precedence', {})
    modes: Dict[int, List[Tuple[int, List[int]]]] = dat.get('job_modes', {})
    H = reader.get_horizon()

    dur = {j: [m[0] for m in modes.get(j, [])] for j in range(1, J+1)}
    reqR = {j: [[m[1][k] if k < R else 0 for k in range(R)] for m in modes.get(j, [])]
            for j in range(1, J+1)}
    reqN = {j: [[m[1][R+k] if (R+k) < len(m[1]) else 0 for k in range(N)] for m in modes.get(j, [])]
            for j in range(1, J+1)}

    # bảo đảm có mode dummy nếu thiếu
    for j in range(1, J+1):
        if len(dur[j]) == 0:
            dur[j] = [0]
            reqR[j] = [[0]*R]
            reqN[j] = [[0]*N]

    # ES/LS: nếu file không có, dùng ES=0; LS=H - min duration
    ES = {j: 0 for j in range(1, J+1)}
    LS = {j: max(0, H - min(dur[j])) for j in range(1, J+1)}

    return J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H, ES, LS

def rtw_indices_for(i, o, tau, ES, LS, dur):
    """RTW(i,o,τ) = các t sao cho job i start ở t sẽ phủ thời điểm τ"""
    d = dur[i][o]
    lo = max(ES[i], tau - d + 1)
    hi = min(LS[i], tau)
    if lo > hi:
        return []
    return list(range(lo, hi+1))

# -------------------------
# Solver (formulation 3.1–3.7)
# -------------------------
def solve_one(mm_path: str, timeout_ms=600_000):
    reader = MRCPSPDataReader(mm_path)
    J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H, ES, LS = build_instance(reader)

    opt = Optimize()
    if timeout_ms is not None:
        opt.set(timeout=timeout_ms)

    # Biến Bool: x[i][t][o] = 1 ⇔ “i start=t, mode=o”
    x = {i: {t: {o: Bool(f"x_{i}_{t}_{o}") for o in range(len(dur[i]))}
             for t in range(ES[i], LS[i]+1)}
         for i in range(1, J+1)}
    # sm[i][o] = 1 ⇔ “i chọn mode o”  (để khớp (3.5))
    sm = {i: {o: Bool(f"sm_{i}_{o}") for o in range(len(dur[i]))} for i in range(1, J+1)}
    M = Int("M"); opt.add(M >= 0)

    # (3.1) S_0 = 0  (giả định job 1 là supersource có dur=0)
    if 1 in x:
        # ép start=0 cho mọi mode của job 1 (nếu có)
        for o in range(len(dur[1])):
            # Exactly-one theo (3.2)–(3.3) đảm bảo chỉ một mode được chọn
            # ép x_{1,t!=0,o}=0 và cho phép x_{1,0,o}
            for t in list(x[1].keys()):
                if t != 0:
                    opt.add( ~x[1][t][o] )

    # (3.2)–(3.3) biên sớm–muộn và (Exactly-one start & mode) trên x
    for i in range(1, J+1):
        lits = []
        for t in range(ES[i], LS[i]+1):
            for o in range(len(dur[i])):
                lits.append(x[i][t][o])
        # Exactly-one: 1) Ít nhất một
        opt.add(bool_sum(lits) == 1)

    # Liên kết sm_{i,o} ↔ ∨_t x_{i,t,o}  (để dùng trong (3.5), (3.7))
    for i in range(1, J+1):
        for o in range(len(dur[i])):
            ors = [x[i][t][o] for t in range(ES[i], LS[i]+1)]
            opt.add( sm[i][o] == Or(ors) )

    # (3.5) ∑_o sm_{i,o} = 1
    for i in range(1, J+1):
        # ít nhất 1
        mos = [sm[i][o] for o in range(len(dur[i]))]
        if mos:
            opt.add(bool_sum(mos) == 1)

    # (3.4) Precedence (i → j): nếu x_{i,t,o}=1 thì mọi start của j ở t'< t+d_{i,o} đều bị cấm
    for i in range(1, J+1):
        for j2 in prec.get(i, []):
            for o in range(len(dur[i])):
                d = dur[i][o]
                for t in range(ES[i], LS[i]+1):
                    forbid = []
                    up_to = min(LS[j2], t + d - 1)
                    for t2 in range(ES[j2], up_to+1):
                        for o2 in range(len(dur[j2])):
                            forbid.append(~x[j2][t2][o2])
                    if forbid:
                        opt.add( Implies(x[i][t][o], And(forbid)) )

    # (3.6) Renewable theo thời điểm τ, dùng RTW: ∑_{i,o} b_{i,k,o} * ∑_{t∈RTW(i,o,τ)} x_{i,t,o} ≤ B_k
    for k in range(R):
        for tau in range(0, H+1):
            terms = []
            for i in range(1, J+1):
                for o in range(len(dur[i])):
                    coef = reqR[i][o][k]
                    if coef == 0:
                        continue
                    T = rtw_indices_for(i, o, tau, ES, LS, dur)
                    if not T:
                        continue
                    terms.append( coef * Sum([If(x[i][t][o], 1, 0) for t in T]) )
            if terms:
                opt.add( Sum(terms) <= R_cap[k] )

    # (3.7) Nonrenewable toàn cục: ∑_{i,o} b_{i,k,o} * sm_{i,o} ≤ B_k
    for k in range(N):
        # m_{i,k} và B'_k
        mins = {}
        for i in range(1, J + 1):
            mins[i] = min(reqN[i][o][k] for o in range(len(reqN[i]))) if len(reqN[i]) else 0
        Bk_reduced = N_cap[k] - sum(mins.values())
        if Bk_reduced < 0:
            #UNSAT
            opt.add(False)
            continue

        # ∑ δ_{i,k,o} sm_{i,o} ≤ B'_k, với δ = b - m_{i,k}
        terms = []
        for i in range(1, J + 1):
            for o in range(len(reqN[i])):
                delta = reqN[i][o][k] - mins[i]
                if delta > 0:
                    terms.append(If(sm[i][o], delta, 0))
                # delta==0 không cần đưa vào tổng
        opt.add(Sum(terms) <= Bk_reduced)

    # Makespan & mục tiêu: M ≥ t + d_{i,o} với cặp (t,o) được chọn của từng i; minimize M
    for i in range(1, J+1):
        expr = Sum([ (t + dur[i][o]) * If(x[i][t][o], 1, 0)
                     for t in range(ES[i], LS[i]+1)
                     for o in range(len(dur[i])) ])
        opt.add(M >= expr)
    opt.minimize(M)

    # ---------------- Solve & print ----------------
    num_constraints = len(opt.assertions())
    # đếm biến ~ số Bool x + Bool sm + 1 biến Int M (xấp xỉ)
    num_variables = sum(len(x[i][t]) for i in x for t in x[i]) + sum(len(sm[i]) for i in sm) + 1

    t0 = time.time()
    res = opt.check()
    solve_time = time.time() - t0

    if res != sat:
        print("✗ UNSAT/UNKNOWN")
        print(f"Tổng ràng buộc (assertions): {num_constraints}")
        print(f"Tổng biến quyết định    : {num_variables}")
        print(f"Total solving time: {solve_time:.2f}s")
        return None

    m = opt.model()
    ms = m[M].as_long()

    # Lấy lịch (job, mode, start, dur, finish, resources)
    schedule = []
    for i in range(1, J+1):
        start, mode_idx = None, None
        for t in range(ES[i], LS[i]+1):
            for o in range(len(dur[i])):
                if m.evaluate(x[i][t][o], model_completion=True):
                    if bool(m.eval(x[i][t][o])):
                        start, mode_idx = t, o
                        break
            if start is not None: break
        d = dur[i][mode_idx]
        finish = start + d
        rvec = []
        rvec += [reqR[i][mode_idx][k] for k in range(R)]
        rvec += [reqN[i][mode_idx][k] for k in range(N)]
        schedule.append((i, mode_idx, start, d, finish, rvec))
    schedule.sort(key=lambda a: (a[2], a[0]))

    # ----- pretty print -----
    print("=== SOLUTION ===")
    print(f"Makespan: {ms}\n")
    hdrR = [f"R{k+1}" for k in range(R)]
    hdrN = [f"N{k+1}" for k in range(N)]
    print("Job   Mode   Start   Duration   Finish   " +
          ("Resources" if not hdrR and not hdrN else f"Resources ({' '.join(hdrR+hdrN)})"))
    print("-"*65)
    for (j, o, st, du, ft, rv) in schedule:
        rstr = "  ".join(f"{v:>2d}" for v in rv) if rv else ""
        print(f"{j:<5d}{(o+1):<7d}{st:<8d}{du:<11d}{ft:<9d} {rstr}")

    # ----- validate nhanh -----
    print("\n=== VALIDATING SOLUTION ===")
    print(f"Actual makespan from solution: {max(ft for *_, ft, _ in schedule)}\n")

    # precedence
    ok_prec = True
    for i in range(1, J+1):
        succs = reader.data.get('precedence', {}).get(i, [])
        if not succs: continue
        st_i = next(st for (j, o, st, du, ft, rv) in schedule if j == i)
        o_i  = next(o for (j, o, st, du, ft, rv) in schedule if j == i)
        di   = dur[i][o_i]
        for j2 in succs:
            st_j = next(st for (jj, oo, st, du, ft, rv) in schedule if jj == j2)
            if st_j < st_i + di: ok_prec = False; break
        if not ok_prec: break
    print("  ✓ All precedence constraints satisfied" if ok_prec else "  ✗ Violation found")

    # renewable
    ok_R = True
    if R > 0:
        print("\nChecking renewable resource constraints...")
        for tau in range(ms+1):
            for k in range(R):
                use = 0
                for (j, o, st, du, ft, rv) in schedule:
                    if st <= tau < ft:
                        use += reqR[j][o][k]
                if use > R_cap[k]: ok_R = False; break
            if not ok_R: break
        print("  ✓ All renewable resource constraints satisfied" if ok_R else "  ✗ Violation found")
    else:
        print("\n(No renewable resources)")

    # nonrenewable
    ok_N = True
    if N > 0:
        print("\nChecking non-renewable resource constraints...")
        for k in range(N):
            total = sum(reqN[j][o][k] for (j,o,st,du,ft,rv) in schedule)
            if total > N_cap[k]: ok_N = False; break
        print("  ✓ All non-renewable resource constraints satisfied" if ok_N else "  ✗ Violation found")
    else:
        print("\n(No non-renewable resources)")

    print("\n" + ("✓ Solution is VALID!" if (ok_prec and ok_R and ok_N) else "✗ Solution is NOT valid.") + "\n")
    print(f"✓ Successfully found optimal makespan = {ms}")
    print(f"Tổng ràng buộc: {len(opt.assertions())}")
    print(f"Tổng biến quyết định    : {num_variables}")
    print(f"Total solving time: {solve_time:.2f}s")

    return dict(makespan=ms, schedule=schedule,
                num_constraints=len(opt.assertions()),
                num_variables=num_variables, solve_time=solve_time)

# -------------------------
if __name__ == "__main__":
    DEFAULT_INSTANCE = "data/j10/j1010_1.mm"

    print("="*100)
    print("RUN ONE INSTANCE (Z3 SMT — formulation 3.1–3.7)")
    print("="*100)
    print(f"Instance: {DEFAULT_INSTANCE}\n")
    solve_one(DEFAULT_INSTANCE, timeout_ms=600_000)
