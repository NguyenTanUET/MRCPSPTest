import os, subprocess


def write_param(enc, out_path):
    """
    Ghi instance.param cho Savile Row từ encoder đang có:
    - enc.jobs, enc.horizon, enc.renewable_resources, enc.nonrenewable_resources
    - enc.job_modes[j][m] = (duration, [req_ren..., req_non...])
    - enc.R_capacity[], enc.N_capacity[]
    - enc.u_vars mask: key tồn tại => hợp lệ
    """
    J = enc.jobs
    H = enc.horizon
    R = enc.renewable_resources
    N = enc.nonrenewable_resources
    Mmax = max(len(enc.job_modes[j]) for j in range(1, J + 1)) if J > 0 else 0

    # nModes[j]
    nModes = [len(enc.job_modes[j]) for j in range(1, J + 1)]

    # reqRen[j,m,k], reqNon[j,m,k]  (Essence 1-based j,m,k)
    reqRen = [[[0] * (R) for _ in range(Mmax)] for __ in range(J)]
    reqNon = [[[0] * (N) for _ in range(Mmax)] for __ in range(J)]
    for j in range(1, J + 1):
        for m in range(len(enc.job_modes[j])):
            vec = enc.job_modes[j][m][1]  # demands vector
            # renewables
            for k in range(R):
                v = vec[k] if len(vec) > k and vec[k] is not None else 0
                reqRen[j - 1][m][k] = int(v)
            # non-renewables
            for k in range(N):
                idx = R + k
                v = vec[idx] if len(vec) > idx and vec[idx] is not None else 0
                reqNon[j - 1][m][k] = int(v)

    # capacities
    capRen = [int(x) for x in enc.R_capacity]
    capNon = [int(x) for x in enc.N_capacity]

    # validU[j,t,m]: 1 nếu U tồn tại (đúng như bạn dùng ở add_process_variable_constraints)
    validU = [[[0] * Mmax for _ in range(H + 1)] for __ in range(J)]
    for j in range(1, J + 1):
        for t in range(H + 1):
            for m in range(len(enc.job_modes[j])):
                if (j in enc.u_vars) and (t in enc.u_vars[j]) and (m in enc.u_vars[j][t]):
                    validU[j - 1][t][m] = 1

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
        _dump_3d(f, reqRen);
        f.write("\n")

        # reqNon
        f.write("letting reqNon be ")
        _dump_3d(f, reqNon);
        f.write("\n")

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
        _dump_3d(f, validU);
        f.write("\n")


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
    param_file = os.path.abspath(param_file)
    dimacs_out = os.path.abspath(dimacs_out)
    aux_out = os.path.abspath(aux_out)
    os.makedirs(os.path.dirname(dimacs_out), exist_ok=True)

    # Thử nhiều cách để tránh lỗi Minion
    cmd = [
        "java", "-jar", jar,
        "-in-eprime", model_eprime,
        "-in-param", param_file,
        "-sat",
        "-out-sat", dimacs_out,
        "-save-symbols",
        "-out-aux", aux_out,
        "-O0",  # Tắt optimization để tránh gọi Minion
        "-no-bound-vars",  # Tắt domain filtering
    ]

    # Bỏ extra_flags nếu có -O2 hoặc -S1
    if extra_flags:
        filtered_flags = []
        for flag in extra_flags:
            if not flag.startswith("-O") and not flag.startswith("-S"):
                filtered_flags.append(flag)
        if filtered_flags:
            cmd.extend(filtered_flags)

    # Chạy với error handling
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        print("Savile Row completed successfully")
    except subprocess.CalledProcessError as e:
        print(f"Savile Row stderr: {e.stderr}")
        # Kiểm tra nếu file DIMACS đã được tạo thành công
        if os.path.exists(dimacs_out) and os.path.getsize(dimacs_out) > 0:
            print("DIMACS file was created despite the error, continuing...")
        else:
            raise e


def parse_sr_varmap(varmap_path: str):
    """
    Parse varmap từ DIMACS file comments thay vì aux file
    Vì aux file là Java serialized object
    """
    import re
    import os

    # Thay đổi: đọc từ DIMACS file thay vì aux
    dimacs_path = varmap_path.replace('.aux', '.dimacs')

    if not os.path.exists(dimacs_path):
        print(f"Warning: DIMACS file not found at {dimacs_path}")
        return {}, {}

    sm_map, u_map = {}, {}

    try:
        with open(dimacs_path, 'r', encoding='utf-8') as f:
            current_var_name = None

            for line_num, line in enumerate(f):
                line = line.strip()

                # Stop after processing reasonable number of comment lines
                if line_num > 500000:  # Safety limit
                    break

                # Stop when we hit the problem line or non-comment
                if line.startswith('p cnf'):
                    break

                if not line.startswith('c'):
                    continue

                # Look for variable encoding line
                if 'Encoding variable:' in line:
                    # Extract variable name
                    m = re.search(r'Encoding variable: (\S+)', line)
                    if m:
                        current_var_name = m.group(1)

                # Look for SAT variable assignment
                elif 'Var represented with SAT variable' in line and current_var_name:
                    m = re.search(r'SAT variable (\d+)', line)
                    if m:
                        sat_var = int(m.group(1))

                        # Parse U variable (with padded zeros)
                        if current_var_name.startswith('U_'):
                            parts = current_var_name[2:].split('_')
                            if len(parts) == 3:
                                j = int(parts[0])
                                t = int(parts[1])
                                mode = int(parts[2])
                                u_map[(j, t, mode)] = sat_var

                        # Parse SM variable (with padded zeros)
                        elif current_var_name.startswith('SM_'):
                            parts = current_var_name[3:].split('_')
                            if len(parts) == 2:
                                j = int(parts[0])
                                mode = int(parts[1])
                                sm_map[(j, mode)] = sat_var

                        current_var_name = None

        print(f"Parsed from DIMACS: {len(sm_map)} SM vars and {len(u_map)} U vars")

        # Debug: print some samples
        if sm_map:
            sample_sm = list(sm_map.items())[:3]
            print(f"  Sample SM mappings: {sample_sm}")
        if u_map:
            sample_u = list(u_map.items())[:3]
            print(f"  Sample U mappings: {sample_u}")

        return sm_map, u_map

    except Exception as e:
        print(f"Error parsing DIMACS file: {e}")
        import traceback
        traceback.print_exc()
        return {}, {}