"""
Fixed MRCPSP Data Reader - đọc horizon trực tiếp từ file .mm
"""

class MRCPSPDataReader:
    """Đọc dữ liệu MRCPSP từ file .mm"""

    def __init__(self, filename):
        self.filename = filename
        self.data = self.read_file()

    def read_file(self):
        """Đọc và parse file .mm"""
        with open(self.filename, 'r') as f:
            content = f.read()

        lines = [line.rstrip() for line in content.split('\n')]
        data = {}
        idx = 0

        # Skip header lines and read basic info
        while idx < len(lines):
            line = lines[idx].strip()

            # Read number of jobs
            if line.startswith("jobs (incl. supersource/sink"):
                parts = line.split()
                total_jobs = int(parts[-1])
                data['num_jobs'] = total_jobs

            # Read horizon directly from file
            elif line.startswith("horizon"):
                parts = line.split()
                horizon = int(parts[-1])
                data['horizon'] = horizon
                print(f"Read horizon from file: {horizon}")

            # Resource information
            elif "- renewable" in line:
                parts = line.split()
                data['num_renewable'] = int(parts[3])
            elif "- nonrenewable" in line:
                parts = line.split()
                data['num_nonrenewable'] = int(parts[3])
            elif line.startswith("PRECEDENCE RELATIONS:"):
                idx += 1
                break
            idx += 1

        # Read precedence relations
        data['precedence'] = {}
        data['num_modes'] = {}

        while idx < len(lines):
            line = lines[idx].strip()
            if line.startswith("REQUESTS/DURATIONS:"):
                break
            if line and not line.startswith("jobnr."):
                parts = line.split()
                if len(parts) >= 3:
                    job_id = int(parts[0])
                    num_modes = int(parts[1])
                    num_successors = int(parts[2])

                    successors = []
                    for i in range(3, 3 + num_successors):
                        if i < len(parts):
                            successors.append(int(parts[i]))

                    data['precedence'][job_id] = successors
                    data['num_modes'][job_id] = num_modes
            idx += 1

        # Skip to job modes section
        while idx < len(lines):
            line = lines[idx].strip()
            if line.startswith("jobnr. mode duration"):
                idx += 2  # Skip header and separator line
                break
            idx += 1

        # Read job modes
        data['job_modes'] = {}
        for j in range(1, data['num_jobs'] + 1):
            data['job_modes'][j] = []

        current_job_id = None

        while idx < len(lines):
            line = lines[idx]
            stripped_line = line.strip()

            if stripped_line.startswith("RESOURCEAVAILABILITIES:"):
                break

            if not stripped_line or stripped_line.startswith("*") or stripped_line.startswith("-"):
                idx += 1
                continue

            parts = stripped_line.split()
            if len(parts) >= 6:
                try:
                    # Determine number of resources
                    num_renewable = data.get('num_renewable', 2)
                    num_nonrenewable = data.get('num_nonrenewable', 2)
                    total_resources = num_renewable + num_nonrenewable

                    if len(parts) == total_resources + 3:
                        # Job line with all info
                        current_job_id = int(parts[0])
                        mode_id = int(parts[1])
                        duration = int(parts[2])
                        resources = [int(parts[3+i]) for i in range(total_resources)]

                        if current_job_id <= data['num_jobs']:
                            data['job_modes'][current_job_id].append((duration, resources))

                    elif len(parts) == total_resources + 2 and current_job_id is not None:
                        # Mode line (continuation of previous job)
                        mode_id = int(parts[0])
                        duration = int(parts[1])
                        resources = [int(parts[2+i]) for i in range(total_resources)]

                        if current_job_id <= data['num_jobs']:
                            data['job_modes'][current_job_id].append((duration, resources))

                except (ValueError, IndexError) as e:
                    pass

            idx += 1

        # Read resource availabilities
        while idx < len(lines):
            line = lines[idx].strip()
            if line and not line.startswith("*") and not line.startswith("R "):
                parts = line.split()

                # Read based on actual number of resources
                num_renewable = data.get('num_renewable', 2)
                num_nonrenewable = data.get('num_nonrenewable', 2)

                if len(parts) >= num_renewable + num_nonrenewable:
                    try:
                        data['renewable_capacity'] = [int(parts[i]) for i in range(num_renewable)]
                        data['nonrenewable_capacity'] = [int(parts[num_renewable + i]) for i in range(num_nonrenewable)]
                        break
                    except ValueError:
                        pass
            idx += 1

        return data

    def get_horizon(self):
        """
        Lấy horizon từ data đã đọc từ file
        Nếu không có trong file, tính dựa trên tổng duration
        """
        # Ưu tiên lấy từ file
        if 'horizon' in self.data:
            return self.data['horizon']

        # Fallback: tính dựa trên tổng duration
        print("Warning: Horizon not found in file, calculating based on durations...")
        total_duration = 0
        for j in range(1, self.data['num_jobs'] + 1):
            if j in self.data['job_modes'] and self.data['job_modes'][j]:
                max_duration = max(mode[0] for mode in self.data['job_modes'][j])
                total_duration += max_duration

        calculated_horizon = total_duration
        print(f"Calculated horizon: {calculated_horizon}")
        return calculated_horizon

    def print_summary(self):
        """In tóm tắt thông tin đã đọc"""
        print("\n=== DATA SUMMARY ===")
        print(f"File: {self.filename}")
        print(f"Number of jobs: {self.data.get('num_jobs', 'N/A')}")
        print(f"Horizon: {self.get_horizon()}")
        print(f"Renewable resources: {self.data.get('num_renewable', 'N/A')}")
        print(f"Non-renewable resources: {self.data.get('num_nonrenewable', 'N/A')}")

        if 'renewable_capacity' in self.data:
            print(f"Renewable capacity: {self.data['renewable_capacity']}")
        if 'nonrenewable_capacity' in self.data:
            print(f"Non-renewable capacity: {self.data['nonrenewable_capacity']}")

        # Show sample precedence
        print("\nSample precedence relations (first 5 jobs):")
        for j in range(1, min(6, self.data.get('num_jobs', 0) + 1)):
            if j in self.data.get('precedence', {}):
                print(f"  Job {j} → {self.data['precedence'][j]}")

        # Show sample job modes
        print("\nSample job modes (first 3 jobs with modes):")
        count = 0
        for j in range(1, self.data.get('num_jobs', 0) + 1):
            if j in self.data.get('job_modes', {}) and self.data['job_modes'][j]:
                print(f"  Job {j}: {len(self.data['job_modes'][j])} modes")
                for i, (dur, res) in enumerate(self.data['job_modes'][j]):
                    print(f"    Mode {i+1}: duration={dur}, resources={res}")
                count += 1
                if count >= 3:
                    break


def compare_reader_versions():
    """So sánh reader cũ và mới"""

    filename = "data/j30/j301_1.mm"

    print("=" * 80)
    print("COMPARING OLD vs NEW READER")
    print("=" * 80)

    try:
        # New reader
        print("\n--- NEW READER ---")
        new_reader = MRCPSPDataReader(filename)
        new_horizon = new_reader.get_horizon()
        print(f"Horizon from new reader: {new_horizon}")

        # Check if horizon matches file
        with open(filename, 'r') as f:
            for line in f:
                if 'horizon' in line and ':' in line:
                    actual_horizon = int(line.split()[-1])
                    print(f"Actual horizon in file: {actual_horizon}")

                    if new_horizon == actual_horizon:
                        print("✓ Reader correctly reads horizon from file!")
                    else:
                        print("✗ Mismatch in horizon values!")
                    break

    except Exception as e:
        print(f"Error: {e}")


if __name__ == "__main__":

    print("\n" + "=" * 80)

    # So sánh versions
    compare_reader_versions()