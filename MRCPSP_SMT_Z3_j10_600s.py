# ================== BATCH RUNNER (Z3, chống tràn RAM) ==================
from pathlib import Path
from typing import Dict, List, Tuple
import time, csv, gc, os
from datetime import datetime
from z3 import Bool, Int, If, Or, And, Sum, Optimize, Implies, sat, set_param

# ---- đọc dữ liệu .mm (giữ nguyên reader của bạn) ----
from MRCPSP_Basic import MRCPSPDataReader
import resource

def _worker_unpack(arg_tuple):
    return _worker_entry(*arg_tuple)

def bool_sum(lits):
    return Sum([If(l, 1, 0) for l in lits])

def _limit_process_memory(memory_limit_mb: int):
    try:
        byte_limit = int(memory_limit_mb) * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (byte_limit, byte_limit))
    except Exception:
        pass

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

    dur = {j: [m[0] for m in modes.get(j, [])] for j in range(1, J+1)}
    reqR = {j: [[m[1][k] if k < R else 0 for k in range(R)] for m in modes.get(j, [])] for j in range(1, J+1)}
    reqN = {j: [[m[1][R+k] if (R+k) < len(m[1]) else 0 for k in range(N)] for m in modes.get(j, [])] for j in range(1, J+1)}

    for j in range(1, J+1):
        if len(dur[j]) == 0:
            dur[j] = [0]
            reqR[j] = [[0]*R]
            reqN[j] = [[0]*N]

    ES = {j: 0 for j in range(1, J+1)}
    LS = {j: max(0, H - min(dur[j])) for j in range(1, J+1)}
    return J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H, ES, LS

def _rtw_indices_for(i, o, tau, ES, LS, dur):
    d = dur[i][o]
    lo = max(ES[i], tau - d + 1)
    hi = min(LS[i], tau)
    if lo > hi:
        return []
    return list(range(lo, hi+1))

def solve_one_instance_z3(mm_path: str, timeout_s: int = 600, memory_limit_mb: int | None = None):
    """
    One-shot Optimize (minimize M) — nhanh như chạy lẻ.
    Trả về dict: instance, horizon, variables, clauses, makespan, status, Solve time, timeout
    """
    # (tuỳ chọn) set soft limit cho Z3
    if memory_limit_mb:
        try:
            from z3 import set_param
            set_param('memory_max_size', int(memory_limit_mb) * 1024 * 1024)  # bytes
        except Exception:
            pass

    t0 = time.time()
    reader = MRCPSPDataReader(mm_path)
    J, R, N, R_cap, N_cap, prec, dur, reqR, reqN, H, ES, LS = _build_instance(reader)

    opt = Optimize()
    opt.set(timeout=timeout_s * 1000)

    # Biến
    x = {i: {t: {o: Bool(f"x_{i}_{t}_{o}") for o in range(len(dur[i]))}
             for t in range(ES[i], LS[i] + 1)}
         for i in range(1, J + 1)}
    sm = {i: {o: Bool(f"sm_{i}_{o}") for o in range(len(dur[i]))}
          for i in range(1, J + 1)}
    S = {i: Int(f"S_{i}") for i in range(1, J + 1)}
    M = Int("M"); opt.add(M >= 0)

    # Helper
    def bool_sum(lits): return Sum([If(l, 1, 0) for l in lits])
    def dur_of(i): return Sum([If(sm[i][o], dur[i][o], 0) for o in range(len(dur[i]))])

    # (3.1) source start=0 (nếu job 1 là nguồn)
    if 1 in x:
        for o in range(len(dur[1])):
            for t in list(x[1].keys()):
                if t != 0:
                    opt.add(~x[1][t][o])

    # (3.2)-(3.3) Exactly-One cho (t,o) của từng job (Sum == 1)
    for i in range(1, J + 1):
        lits = [x[i][t][o] for t in range(ES[i], LS[i] + 1) for o in range(len(dur[i]))]
        if lits:
            opt.add(bool_sum(lits) == 1)

    # sm[i,o] <-> OR_t x[i,t,o]
    for i in range(1, J + 1):
        for o in range(len(dur[i])):
            opt.add(sm[i][o] == Or([x[i][t][o] for t in range(ES[i], LS[i] + 1)]))

    # (3.5) Exactly-One cho mode (Sum == 1) — hoặc có thể bỏ vì đã suy ra từ x
    for i in range(1, J + 1):
        mos = [sm[i][o] for o in range(len(dur[i]))]
        if mos:
            opt.add(bool_sum(mos) == 1)

    # Liên kết S_i với x
    for i in range(1, J + 1):
        opt.add(And(S[i] >= ES[i], S[i] <= LS[i]))
        opt.add(S[i] == Sum([(t) * If(x[i][t][o], 1, 0)
                             for t in range(ES[i], LS[i] + 1)
                             for o in range(len(dur[i]))]))

    # (3.4) precedence: S_j >= S_i + dur(i)
    for i in range(1, J + 1):
        for j2 in prec.get(i, []):
            opt.add(S[j2] >= S[i] + dur_of(i))

    # (3.6) renewable: theo RTW ở mọi τ ∈ [0..H]
    # (one-shot như bản chạy lẻ — nhanh rồi; nếu muốn thêm boost, có thể dùng τ ∈ [0..M] với M là upper bound heur.)
    for k in range(R):
        for tau in range(0, H + 1):
            terms = []
            for i in range(1, J + 1):
                for o in range(len(dur[i])):
                    r = reqR[i][o][k]
                    if r == 0:
                        continue
                    T = _rtw_indices_for(i, o, tau, ES, LS, dur)
                    if not T:
                        continue
                    terms.append(r * Sum([If(x[i][t][o], 1, 0) for t in T]))
            if terms:
                opt.add(Sum(terms) <= R_cap[k])

    # (3.7) nonrenewable với EO-reduction (§4.4.1/§3.2.5)
    for k in range(N):
        mins = {i: (min(reqN[i][o][k] for o in range(len(reqN[i]))) if len(reqN[i]) else 0)
                for i in range(1, J + 1)}
        Bk_reduced = N_cap[k] - sum(mins.values())
        if Bk_reduced < 0:
            opt.add(False)
            continue
        terms = []
        for i in range(1, J + 1):
            for o in range(len(reqN[i])):
                delta = reqN[i][o][k] - mins[i]
                if delta > 0:
                    terms.append(If(sm[i][o], delta, 0))
        opt.add(Sum(terms) <= Bk_reduced)

    # Mục tiêu và ràng buộc makespan
    for i in range(1, J + 1):
        opt.add(M >= S[i] + dur_of(i))
    opt.minimize(M)

    # Solve
    num_constraints = len(opt.assertions())
    num_variables = (sum(len(x[i][t]) for i in x for t in x[i]) + sum(len(sm[i]) for i in sm) + len(S) + 1)

    res = opt.check()
    solve_time = time.time() - t0

    if res != sat:
        return {"instance": Path(mm_path).name, "horizon": reader.get_horizon(),
                "variables": num_variables, "clauses": num_constraints,
                "makespan": "", "status": "Infeasible", "Solve time": f"{solve_time:.2f}",
                "timeout": "Yes" if solve_time >= timeout_s else "No"}

    m = opt.model()
    ms = m[M].as_long()

    return {
        "instance": Path(mm_path).name,
        "horizon": reader.get_horizon(),
        "variables": num_variables,
        "clauses": num_constraints,    # với SMT: đếm assertions
        "makespan": ms,
        "status": "Optimal",
        "Solve time": f"{solve_time:.2f}",
        "timeout": "No" if solve_time < timeout_s else "Yes",
    }


# ---- chạy 1 instance trong PROCESS RIÊNG để chống tràn RAM ----
def _worker_entry(mm_path: str, timeout_s: int, memory_limit_mb: int | None):
    if memory_limit_mb:
        _limit_process_memory(memory_limit_mb)
    try:
        row = solve_one_instance_z3(mm_path, timeout_s=timeout_s, memory_limit_mb=memory_limit_mb)
    except Exception as e:
        row = {"instance": Path(mm_path).name, "horizon": "", "variables": "",
               "clauses": "", "makespan": "", "status": f"Error:{e}", "Solve time": "", "timeout": "No"}
    return row

def run_batch_smt(
    data_dir="data/j10",
    out_dir="result/j10",
    timeout_s=600,
    batch_flush=10,
    process_isolation=True,     # chống tràn RAM: chạy mỗi instance trong 1 process
    memory_limit_mb=None        # soft limit cho Z3 (MB)
):
    data_path = Path(data_dir)
    out_path = Path(out_dir)
    out_path.mkdir(parents=True, exist_ok=True)

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    csv_file = out_path / f"Z3_results_{data_path.name}_{ts}.csv"

    fields = ["instance", "horizon", "variables", "clauses",
              "makespan", "status", "Solve time", "timeout"]

    mm_files = sorted(data_path.glob("*.mm"))
    print(f"Found {len(mm_files)} instances in {data_path}")

    # ghi header
    with csv_file.open("w", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=fields).writeheader()

    results = []
    if process_isolation:
        import multiprocessing as mp
        ctx = mp.get_context("spawn")
        with ctx.Pool(processes=1) as pool:
            args = [(str(mm), timeout_s, memory_limit_mb) for mm in mm_files]
            for idx, row in enumerate(pool.imap_unordered(_worker_unpack, args), start=1):
                results.append(row)
                print(f"[{idx}/{len(mm_files)}] {row['instance']} -> {row['status']} (ms={row.get('makespan', '')})")
                if idx % batch_flush == 0:
                    with csv_file.open("a", newline="", encoding="utf-8") as f:
                        csv.DictWriter(f, fieldnames=fields).writerows(results[-batch_flush:])
                    print(f"  ✓ Đã lưu tạm {batch_flush} dòng vào {csv_file}")
    else:
        # chạy inline (nhanh hơn) nhưng nhớ dọn RAM
        for idx, mm in enumerate(mm_files, start=1):
            print(f"[{idx}/{len(mm_files)}] Solving {mm.name} ...")
            row = solve_one_instance_z3(str(mm), timeout_s=timeout_s, memory_limit_mb=memory_limit_mb)
            results.append(row)

            if idx % batch_flush == 0:
                with csv_file.open("a", newline="", encoding="utf-8") as f:
                    csv.DictWriter(f, fieldnames=fields).writerows(results[-batch_flush:])
                print(f"  ✓ Đã lưu tạm {batch_flush} dòng vào {csv_file}")

            # dọn dẹp
            gc.collect()

    # ghi phần còn lại
    rem = len(results) % batch_flush
    if rem:
        with csv_file.open("a", newline="", encoding="utf-8") as f:
            csv.DictWriter(f, fieldnames=fields).writerows(results[-rem:])
        print(f"  ✓ Đã lưu phần còn lại ({rem} dòng) vào {csv_file}")

    print(f"\nHoàn tất. Kết quả lưu tại: {csv_file}")
    return csv_file

if __name__ == "__main__":
    # Ví dụ chạy batch giống j10
    run_batch_smt(
        data_dir="data/j10",
        out_dir="result/j10",
        timeout_s=600,
        batch_flush=10,
        process_isolation=True,   # True để chống tràn RAM
        memory_limit_mb=8192      # tuỳ chọn
    )
