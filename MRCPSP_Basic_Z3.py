# MRCPSP_Basic_Z3_fix.py
# Z3 SMT encode for MRCPSP (formulation 3.1–3.7, robust for j10/j30)
# - Exactly-One via sum==1
# - Precedence via S_j >= S_i + dur(i,mode)
# - Renewable via RTW
# - Nonrenewable with EO-reduction (auto-fallback to plain PB if reduction says infeasible)
# - Data guards & helpful logs

from __future__ import annotations
from pathlib import Path
import sys, time
from typing import Dict, List

from z3 import (
    Bool, Int, If, Or, And, Sum, Optimize, sat, set_param, ModelRef
)

# ---- Reader (bạn đã có sẵn) ----
try:
    from MRCPSP_Basic import MRCPSPDataReader
except Exception as e:
    print("Cannot import MRCPSPDataReader:", e)
    sys.exit(1)


# ---------- Helpers ----------
def _bool_sum(lits):  # Sum Bools as Int
    return Sum([If(l, 1, 0) for l in lits])

def _rtw_indices_for(i: int, o: int, tau: int,
                     ES: Dict[int,int], LS: Dict[int,int],
                     dur: Dict[int, List[int]]) -> List[int]:
    d = dur[i][o]
    lo = max(ES[i], tau - d + 1)
    hi = min(LS[i], tau)
    if lo > hi:
        return []
    return list(range(lo, hi+1))


def _build_instance(reader: MRCPSPDataReader):
    dat = reader.data
    J = dat['num_jobs']
    R = dat.get('num_renewable', 0)
    N = dat.get('num_nonrenewable', 0)
    R_cap = dat.get('renewable_capacity', [0]*R)
    N_cap = dat.get('nonrenewable_capacity', [0]*N)
    prec = dat.get('precedence', {})
    modes = dat.get('job_modes', {})
    H = reader.get_horizon()

    # Pack durations + resource vectors, guard for length != R+N
    dur: Dict[int, List[int]] = {}
    reqR: Dict[int, List[List[int]]] = {}
    reqN: Dict[int, List[List[int]]] = {}

    for j in range(1, J+1):
        jmodes = modes.get(j, [])
        dj, rR, rN = [], [], []
        for (d, vec) in jmodes:
            vec = list(vec)
            # Guard length vs R+N
            if len(vec) < R + N:
                vec = vec + [0] * (R + N - len(vec))
                print(f"[WARN] Job {j} mode has {len(vec)-(R+N)} padded zeros to match R+N")
            elif len(vec) > R + N:
                vec = vec[:R+N]
                print(f"[WARN] Job {j} mode had extra columns; truncated to R+N")
            dj.append(d)
            rR.append([vec[k] for k in range(R)])
            rN.append([vec[R+k] for k in range(N)])
        if not dj:
            dj  = [0]
            rR  = [[0]*R]
            rN  = [[0]*N]
        dur[j]  = dj
        reqR[j] = rR
        reqN[j] = rN

    ES = {j: 0 for j in range(1, J+1)}
    LS = {j: max(0, H - (min(dur[j]) if dur[j] else 0)) for j in range(1, J+1)}
    return J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H, ES, LS


def solve_one_instance_z3(mm_path: str, timeout_s: int = 600, memory_limit_mb: int | None = None):
    # ---- Load ----
    reader = MRCPSPDataReader(mm_path)
    H = reader.get_horizon()
    print(f"Read horizon from file: {H}")

    J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H, ES, LS = _build_instance(reader)

    # ---- Z3 setup ----
    if memory_limit_mb:
        try:
            set_param('memory_max_size', int(memory_limit_mb) * 1024 * 1024)  # bytes
        except Exception:
            pass

    opt = Optimize()
    opt.set(timeout=timeout_s * 1000)

    # ---- Variables ----
    x = {i: {t: {o: Bool(f"x_{i}_{t}_{o}") for o in range(len(dur[i]))}
             for t in range(ES[i], LS[i] + 1)}
         for i in range(1, J + 1)}
    sm = {i: {o: Bool(f"sm_{i}_{o}") for o in range(len(dur[i]))}
          for i in range(1, J + 1)}
    S = {i: Int(f"S_{i}") for i in range(1, J + 1)}
    M = Int("M"); opt.add(M >= 0)

    def dur_of(i: int):
        return Sum([If(sm[i][o], dur[i][o], 0) for o in range(len(dur[i]))])

    # ---- Source fix (job 1 at t=0 nếu là supersource) ----
    if 1 in x:
        for o in range(len(dur[1])):
            for t in list(x[1].keys()):
                if t != 0:
                    opt.add(~x[1][t][o])

    # ---- Exactly-One (t,o) ----
    for i in range(1, J+1):
        lits = [x[i][t][o] for t in range(ES[i], LS[i]+1) for o in range(len(dur[i]))]
        if lits:
            opt.add(_bool_sum(lits) == 1)

    # sm[i,o] <-> OR_t x[i,t,o]
    for i in range(1, J+1):
        for o in range(len(dur[i])):
            opt.add(sm[i][o] == Or([x[i][t][o] for t in range(ES[i], LS[i]+1)]))

    # Exactly-One mode (redundant but clarifies)
    for i in range(1, J+1):
        mos = [sm[i][o] for o in range(len(dur[i]))]
        if mos:
            opt.add(_bool_sum(mos) == 1)

    # ---- Start variables S_i ----
    for i in range(1, J+1):
        opt.add(And(S[i] >= ES[i], S[i] <= LS[i]))
        opt.add(S[i] == Sum([
            t * If(x[i][t][o], 1, 0)
            for t in range(ES[i], LS[i]+1)
            for o in range(len(dur[i]))
        ]))

    # ---- Precedence: S_j >= S_i + d_i ----
    for i in range(1, J+1):
        for j2 in prec.get(i, []):
            opt.add(S[j2] >= S[i] + dur_of(i))

    # ---- Renewable RTW (tau in [0..H-1]) ----
    for k in range(R):
        cap = R_cap[k]
        for tau in range(0, H):
            terms = []
            for i in range(1, J+1):
                for o in range(len(dur[i])):
                    r = reqR[i][o][k] if k < len(reqR[i][o]) else 0
                    if r == 0:
                        continue
                    T = _rtw_indices_for(i, o, tau, ES, LS, dur)
                    if not T:
                        continue
                    terms.append(r * Sum([If(x[i][t][o], 1, 0) for t in T]))
            if terms:
                opt.add(Sum(terms) <= cap)

    # ---- Nonrenewable PB with EO-reduction (auto-fallback) ----
    used_fallback = False
    for k in range(N):
        mins = {i: (min(reqN[i][o][k] for o in range(len(reqN[i]))) if len(reqN[i]) else 0)
                for i in range(1, J+1)}
        sum_min = sum(mins.values())
        Bk = N_cap[k]
        Bk_reduced = Bk - sum_min

        if Bk_reduced < 0:
            # Fallback: dùng PB cơ bản thay vì cứng UNSAT
            used_fallback = True
            print(f"[NR-FALLBACK] Sum of minima for N{k+1} = {sum_min} > capacity {Bk}. "
                  f"Using plain PB instead of EO-reduction.")
            opt.add(Sum([
                reqN[i][o][k] * If(sm[i][o], 1, 0)
                for i in range(1, J+1)
                for o in range(len(reqN[i]))
            ]) <= Bk)
        else:
            terms = []
            for i in range(1, J+1):
                for o in range(len(reqN[i])):
                    delta = reqN[i][o][k] - mins[i]
                    if delta > 0:
                        terms.append(If(sm[i][o], delta, 0))
            opt.add(Sum(terms) <= Bk_reduced)

    # ---- Makespan ----
    for i in range(1, J+1):
        opt.add(M >= S[i] + dur_of(i))
    opt.minimize(M)

    # ---- Solve ----
    t0 = time.time()
    res = opt.check()
    solve_time = time.time() - t0

    num_constraints = len(opt.assertions())
    num_bool_x = sum(len(dur[i]) * (LS[i] - ES[i] + 1) for i in range(1, J+1))
    num_bool_sm = sum(len(dur[i]) for i in range(1, J+1))
    num_variables = num_bool_x + num_bool_sm + len(S) + 1  # + S_i + M

    if res != sat:
        print("✗ UNSAT/UNKNOWN")
        print(f"Tổng ràng buộc (assertions): {num_constraints}")
        print(f"Tổng biến quyết định    : {num_variables}")
        print(f"Total solving time: {solve_time:.2f}s")
        return None

    m: ModelRef = opt.model()
    ms = m[M].as_long()
    print("=== SOLUTION ===")
    print(f"Makespan: {ms}\n")

    # reconstruct schedule
    def sel_mode(i: int) -> int:
        for o in range(len(dur[i])):
            if m.evaluate(sm[i][o], model_completion=True) is True:
                return o
        return 0

    schedule = []
    for i in range(1, J+1):
        s = m.evaluate(S[i], model_completion=True).as_long()
        o = sel_mode(i)
        d = dur[i][o]
        f = s + d
        Rv = reqR[i][o] if i in reqR and o < len(reqR[i]) else [0]*R
        Nv = reqN[i][o] if i in reqN and o < len(reqN[i]) else [0]*N
        schedule.append((i, o+1, s, d, f, Rv, Nv))

    # pretty print (sorted by start)
    print("Job  Mode  Start  Duration  Finish   Resources (R...  N...)")
    print("-"*72)
    for (i, mo, s, d, f, Rv, Nv) in sorted(schedule, key=lambda x: x[2]):
        res_str = " ".join(map(str, Rv + Nv))
        print(f"{i:<4} {mo:<5} {s:<6} {d:<8} {f:<7}  {res_str}")

    # quick checks
    ok = True
    for i in range(1, J+1):
        for j2 in prec.get(i, []):
            si = [row for row in schedule if row[0] == i][0][2]
            di = [row for row in schedule if row[0] == i][0][3]
            sj = [row for row in schedule if row[0] == j2][0][2]
            if sj < si + di:
                ok = False
                print(f"[ERR] precedence violated: {i}->{j2} sj={sj} < si+di={si+di}")
    if ok:
        print("\n✓ Precedence constraints satisfied")

    print(f"\n✓ Successfully found optimal makespan = {ms}")
    print(f"Tổng ràng buộc (assertions): {num_constraints}")
    print(f"Tổng biến quyết định    : {num_variables}")
    print(f"Total solving time: {solve_time:.2f}s")
    return {
        "makespan": ms,
        "variables": num_variables,
        "constraints": num_constraints,
        "time": solve_time,
        "schedule": schedule,
    }


if __name__ == "__main__":
    mm = sys.argv[1] if len(sys.argv) > 1 else "data/j30/j3010_1.mm"
    print("="*100)
    print("RUN ONE INSTANCE (Z3 SMT — formulation 3.1–3.7)")
    print("="*100)
    print("Instance:", mm, "\n")
    solve_one_instance_z3(mm, timeout_s=600, memory_limit_mb=None)
