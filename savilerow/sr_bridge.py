import os, subprocess

def write_param(enc, out_path):
    """
    Ghi instance.param cho Savile Row từ encoder đang có:
    - enc.jobs, enc.horizon, enc.renewable_resources, enc.nonrenewable_resources
    - enc.job_modes[j][m] = (duration, [req_ren..., req_non...])
    - enc.R_capacity[], enc.N_capacity[]
    - enc.u_vars mask: key tồn tại => hợp lệ
    """
    J  = enc.jobs
    H  = enc.horizon
    R  = enc.renewable_resources
    N  = enc.nonrenewable_resources
    Mmax = max(len(enc.job_modes[j]) for j in range(1, J+1)) if J>0 else 0

    # nModes[j]
    nModes = [len(enc.job_modes[j]) for j in range(1, J+1)]

    # reqRen[j,m,k], reqNon[j,m,k]  (Essence 1-based j,m,k)
    # Vector yêu cầu trong code của bạn: renew đứng trước, non-renew đứng sau. :contentReference[oaicite:3]{index=3}
    reqRen = [[[0]*(R) for _ in range(Mmax)] for __ in range(J)]
    reqNon = [[[0]*(N) for _ in range(Mmax)] for __ in range(J)]
    for j in range(1, J+1):
        for m in range(len(enc.job_modes[j])):
            vec = enc.job_modes[j][m][1]  # demands vector
            # renewables
            for k in range(R):
                v = vec[k] if len(vec)>k and vec[k] is not None else 0
                reqRen[j-1][m][k] = int(v)
            # non-renewables
            for k in range(N):
                idx = R + k
                v = vec[idx] if len(vec)>idx and vec[idx] is not None else 0
                reqNon[j-1][m][k] = int(v)

    # capacities
    capRen = [int(x) for x in enc.R_capacity]
    capNon = [int(x) for x in enc.N_capacity]

    # validU[j,t,m]: 1 nếu U tồn tại (đúng như bạn dùng ở add_process_variable_constraints) :contentReference[oaicite:4]{index=4}
    validU = [[[0]*Mmax for _ in range(H+1)] for __ in range(J)]
    for j in range(1, J+1):
        for t in range(H+1):
            for m in range(len(enc.job_modes[j])):
                if (j in enc.u_vars) and (t in enc.u_vars[j]) and (m in enc.u_vars[j][t]):
                    validU[j-1][t][m] = 1

    # Ghi Essence param (định dạng basic)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"language Essence 1.3\n\n")
        f.write(f"letting J be {J}\n")
        f.write(f"letting H be {H}\n")
        f.write(f"letting R be {R}\n")
        f.write(f"letting N be {N}\n")
        f.write(f"letting Mmax be {Mmax}\n\n")

        # nModes
        f.write("letting nModes be [")
        f.write(", ".join(str(x) for x in nModes))
        f.write("]\n\n")

        # reqRen
        f.write("letting reqRen be ")
        _dump_3d(f, reqRen); f.write("\n")

        # reqNon
        f.write("letting reqNon be ")
        _dump_3d(f, reqNon); f.write("\n")

        # capRen
        f.write("letting capRen be [")
        f.write(", ".join(str(x) for x in capRen))
        f.write("]\n")

        # capNon
        f.write("letting capNon be [")
        f.write(", ".join(str(x) for x in capNon))
        f.write("]\n\n")

        # validU
        f.write("letting validU be ")
        _dump_3d(f, validU); f.write("\n")

def _dump_3d(f, arr):
    # Essence: matrix [[...],[...],...]
    f.write("[")
    for i, A in enumerate(arr):
        if i: f.write(", ")
        f.write("[")
        for j, B in enumerate(A):
            if j: f.write(", ")
            f.write("[")
            for k, v in enumerate(B):
                if k: f.write(", ")
                f.write(str(int(v)))
            f.write("]")
        f.write("]")
    f.write("]")


def run_savilerow(model_eprime, param_file, dimacs_out, aux_out,
                  jar_path=None, extra_flags=None):
    import os, subprocess, shlex

    jar = jar_path or os.environ.get("SAVILEROW_JAR")
    if not jar or not os.path.exists(jar):
        candidate = "/home/nguyentan/savilerow-1.10.1-linux/savilerow.jar"
        if os.path.exists(candidate):
            jar = candidate
        else:
            raise FileNotFoundError(
                "Không tìm thấy savilerow.jar (set $SAVILEROW_JAR hoặc truyền jar_path)"
            )

    model_eprime = os.path.abspath(model_eprime)
    param_file   = os.path.abspath(param_file)
    dimacs_out   = os.path.abspath(dimacs_out)
    aux_out      = os.path.abspath(aux_out)
    os.makedirs(os.path.dirname(dimacs_out), exist_ok=True)

    cmd = [
        "java", "-jar", jar,
        "-in-eprime", model_eprime,
        "-in-param",  param_file,
        "-sat",
        "-out-sat",   dimacs_out,
        "-save-symbols",
        "-out-aux",   aux_out,
        "-O2", "-S1",
    ]
    if extra_flags:
        if isinstance(extra_flags, str):
            cmd.extend(shlex.split(extra_flags))
        else:
            cmd.extend(extra_flags)

    subprocess.run(cmd, check=True)

def parse_sr_varmap(varmap_path: str):
    """
    Parse varmap Savile Row -> hai dict:
      - sm_map[(j,m)] = dimacs_id
      - u_map[(j,t,m)] = dimacs_id
    Essence dùng 1-based cho j,m,t.
    """
    import re
    sm_map, u_map = {}, {}
    pat_sm = re.compile(r"SM\[(\d+),\s*(\d+)\]\s*=\s*(\d+)")
    pat_u  = re.compile(r"U\[(\d+),\s*(\d+),\s*(\d+)\]\s*=\s*(\d+)")
    with open(varmap_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            m = pat_sm.search(line)
            if m:
                j, mm, vid = map(int, m.groups())
                sm_map[(j, mm)] = int(vid)
                continue
            m = pat_u.search(line)
            if m:
                j, tt, mm, vid = map(int, m.groups())
                u_map[(j, tt, mm)] = int(vid)
                continue
    return sm_map, u_map