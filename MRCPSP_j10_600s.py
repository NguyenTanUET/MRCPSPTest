import os
import csv
import time
import glob
from datetime import datetime


class MRCPSPDataReader:
    def __init__(self, filename):
        self.filename = filename
        self.data = {}
        self.read_file()

    def read_file(self):
        """Read and parse the MRCPSP instance file"""
        with open(self.filename, 'r') as f:
            lines = f.readlines()

        # Skip header lines
        i = 0
        while i < len(lines) and not lines[i].strip().startswith('projects'):
            i += 1

        # Read basic information
        while i < len(lines):
            line = lines[i].strip()
            if line.startswith('projects'):
                self.data['projects'] = int(line.split(':')[1].strip())
            elif line.startswith('jobs'):
                self.data['jobs'] = int(line.split(':')[1].strip())
            elif line.startswith('horizon'):
                self.data['horizon'] = int(line.split(':')[1].strip())
            elif line.startswith('- renewable'):
                self.data['renewable'] = int(line.split(':')[1].split('R')[0].strip())
            elif line.startswith('- nonrenewable'):
                self.data['nonrenewable'] = int(line.split(':')[1].split('N')[0].strip())
            elif 'PRECEDENCE RELATIONS:' in line:
                i += 2  # Skip header
                break
            i += 1

        # Read precedence relations
        precedence = {}
        while i < len(lines) and not lines[i].strip().startswith('*'):
            line = lines[i].strip()
            if line and not line.startswith('jobnr'):
                parts = line.split()
                if len(parts) >= 3:
                    job = int(parts[0])
                    modes = int(parts[1])
                    num_successors = int(parts[2])
                    successors = []
                    if num_successors > 0 and len(parts) > 3:
                        successors = [int(x) for x in parts[3:3 + num_successors]]
                    precedence[job] = {'modes': modes, 'successors': successors}
            i += 1
        self.data['precedence'] = precedence

        # Skip to REQUESTS/DURATIONS section
        while i < len(lines) and 'REQUESTS/DURATIONS:' not in lines[i]:
            i += 1
        i += 2  # Skip header lines

        # Read job modes and resource requirements
        job_modes = {}
        current_job = None

        while i < len(lines):
            line = lines[i].strip()
            if not line or line.startswith('*'):
                break
            if not line.startswith('-'):
                parts = line.split()
                if len(parts) >= 2:
                    try:
                        job = int(parts[0])
                        mode = int(parts[1])
                        duration = int(parts[2])
                        resources = [int(x) for x in parts[3:]]

                        if job not in job_modes:
                            job_modes[job] = {}
                        job_modes[job][mode] = {
                            'duration': duration,
                            'resources': resources
                        }
                        current_job = job
                    except:
                        pass
            else:
                # Continuation line for modes
                if current_job is not None:
                    parts = line.split()
                    if len(parts) >= 2:
                        try:
                            mode = int(parts[0])
                            duration = int(parts[1])
                            resources = [int(x) for x in parts[2:]]

                            if current_job not in job_modes:
                                job_modes[current_job] = {}
                            job_modes[current_job][mode] = {
                                'duration': duration,
                                'resources': resources
                            }
                        except:
                            pass
            i += 1

        self.data['job_modes'] = job_modes

        # Set resource capacities (assume standard values)
        self.data['R_capacity'] = [10] * self.data['renewable']
        self.data['N_capacity'] = [100] * self.data['nonrenewable']

    def get_horizon(self):
        """Calculate horizon as sum of all job durations (upper bound)"""
        horizon = 0
        for job, modes in self.data['job_modes'].items():
            if modes:  # If job has modes
                min_duration = min(mode_data['duration'] for mode_data in modes.values())
                horizon += min_duration
        return max(horizon, self.data.get('horizon', 0))


def get_j10_files(data_dir="data/j10"):
    """Get all .mm files from j10 directory"""
    pattern = os.path.join(data_dir, "*.mm")
    files = glob.glob(pattern)
    return sorted(files)


def solve_instance(filename, timeout=600):
    """Solve a single MRCPSP instance with timeout"""
    try:
        start_time = time.time()

        # Read instance
        reader = MRCPSPDataReader(filename)
        data = reader.data

        # Create solver
        solver = MRCPSPBlockBasedStaircase(
            jobs=data['jobs'],
            job_modes=data['job_modes'],
            precedence=data['precedence'],
            renewable_resources=data['renewable'],
            nonrenewable_resources=data['nonrenewable'],
            R_capacity=data['R_capacity'],
            N_capacity=data['N_capacity'],
            horizon=reader.get_horizon()
        )

        # Encode the problem
        solver.encode()

        # Get statistics
        num_variables = len(solver.vpool.id2obj)
        num_clauses = len(solver.cnf.clauses) if hasattr(solver.cnf, 'clauses') else 0

        # Solve with timeout
        solution = solver.find_optimal_makespan(timeout=timeout)

        solve_time = time.time() - start_time

        if solution is not None:
            if solution['optimal']:
                status = "optimal"
            else:
                status = "feasible"
        else:
            status = "infeasible"

        timeout_occurred = solve_time >= timeout

        return {
            'instance': os.path.basename(filename),
            'horizon': solver.horizon,
            'variables': num_variables,
            'clauses': num_clauses,
            'status': status,
            'solve_time': solve_time,
            'timeout': "Yes" if timeout_occurred else "No"
        }

    except Exception as e:
        return {
            'instance': os.path.basename(filename),
            'horizon': 0,
            'variables': 0,
            'clauses': 0,
            'status': "error",
            'solve_time': 0,
            'timeout': "No"
        }


def run_j10_experiments(output_file="j10_results.csv", timeout=600):
    """Run all j10 instances and save results to CSV"""
    files = get_j10_files()
    results = []

    print(f"Found {len(files)} instances in data/j10")
    print(f"Each instance will run for maximum {timeout} seconds")
    print(f"Results will be saved to: {output_file}")
    print("-" * 60)

    for i, filename in enumerate(files, 1):
        print(f"Processing {i}/{len(files)}: {os.path.basename(filename)}")

        result = solve_instance(filename, timeout)
        results.append(result)

        print(f"  Status: {result['status']}, Time: {result['solve_time']:.2f}s, "
              f"Variables: {result['variables']}, Clauses: {result['clauses']}")

        # Save intermediate results every 10 instances
        if i % 10 == 0:
            save_results_to_csv(results, f"temp_{output_file}")
            print(f"  Intermediate results saved ({i} instances completed)")

    # Save final results
    save_results_to_csv(results, output_file)

    print("-" * 60)
    print(f"All {len(files)} instances completed!")
    print(f"Final results saved to: {output_file}")

    # Display summary
    display_summary(results)

    return results


def save_results_to_csv(results, filename):
    """Save results to CSV file"""
    fieldnames = ['instance', 'horizon', 'variables', 'clauses', 'status', 'solve_time', 'timeout']

    with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()

        for result in results:
            # Round solve_time to 2 decimal places
            result_copy = result.copy()
            result_copy['solve_time'] = round(result_copy['solve_time'], 2)
            writer.writerow(result_copy)


def display_summary(results):
    """Display summary statistics"""
    total = len(results)
    optimal = len([r for r in results if r['status'] == 'optimal'])
    feasible = len([r for r in results if r['status'] == 'feasible'])
    infeasible = len([r for r in results if r['status'] == 'infeasible'])
    errors = len([r for r in results if r['status'] == 'error'])
    timeouts = len([r for r in results if r['timeout'] == 'Yes'])

    avg_time = sum(r['solve_time'] for r in results) / total if total > 0 else 0
    avg_vars = sum(r['variables'] for r in results) / total if total > 0 else 0
    avg_clauses = sum(r['clauses'] for r in results) / total if total > 0 else 0

    print("\nSUMMARY STATISTICS:")
    print(f"Total instances: {total}")
    print(f"Optimal solutions: {optimal} ({optimal / total * 100:.1f}%)")
    print(f"Feasible solutions: {feasible} ({feasible / total * 100:.1f}%)")
    print(f"Infeasible: {infeasible} ({infeasible / total * 100:.1f}%)")
    print(f"Errors: {errors} ({errors / total * 100:.1f}%)")
    print(f"Timeouts: {timeouts} ({timeouts / total * 100:.1f}%)")
    print(f"Average solve time: {avg_time:.2f}s")
    print(f"Average variables: {avg_vars:.0f}")
    print(f"Average clauses: {avg_clauses:.0f}")


if __name__ == "__main__":
    # Run experiments on all j10 instances
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = f"j10_staircase_results_{timestamp}.csv"

    results = run_j10_experiments(output_file=output_file, timeout=600)