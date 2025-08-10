from dask.bytes.tests.test_compression import test_files

import time
import traceback

def compare_original_vs_blockbased(instance_file):

    # Import các encoders
    from MRCPSTest import MRCPSPDataReader, MRCPSPSATEncoder as OriginalEncoder

    try:
        from Improved_Fix_Root import MRCPSPBlockBasedStaircase
    except ImportError:
        print("Warning: Cannot import MRCPSPBlockBasedStaircase")
        print("Make sure Improved_Fix_Root.py exists in the same directory")
        MRCPSPBlockBasedStaircase = None

    # Read instance
    reader = MRCPSPDataReader(instance_file)

    print(f"\nInstance: {instance_file}")
    print(f"Jobs: {reader.data['num_jobs']}")
    print(f"Horizon: {reader.get_horizon()}")
    print(f"Renewable resources: {reader.data['renewable_capacity']}")
    print(f"Non-renewable resources: {reader.data['nonrenewable_capacity']}")

    makespan = reader.get_horizon()
    print(f"\nTest makespan: {makespan}")

    print("\n" + "=" * 60)
    print("ORIGINAL IMPLEMENTATION (MRCPSPTest.py)")
    print("=" * 60)
    start_time = time.time()
    original_encoder = OriginalEncoder(reader)

    # Create variables and constraints
    original_encoder.cnf.clauses = []  # Reset

    # Reset variable pool
    original_encoder.vpool.top = 0


    original_encoder.create_variables()
    original_encoder.add_start_time_constraints()
    original_encoder.add_mode_selection_constraints()
    original_encoder.add_precedence_constraints()
    original_encoder.add_running_variable_constraints()
    original_encoder.add_renewable_resource_constraints()
    original_encoder.add_nonrenewable_resource_constraints()
    original_encoder.add_makespan_constraint(makespan)

    original_time = time.time() - start_time

    # Get variable count
    var_count = original_encoder.vpool.top

    original_stats = {
        'variables': var_count,
        'clauses': len(original_encoder.cnf.clauses),
        'time': original_time
    }

    print(f"Variables: {original_stats['variables']}")
    print(f"Clauses: {original_stats['clauses']}")
    print(f"Encoding time: {original_stats['time']:.3f}s")

    # Breakdown by constraint type (approximate)
    print("\nConstraint breakdown:")
    if hasattr(original_encoder, 's_vars'):
        print(f"  - Start time vars (s_j,t): ~{len(original_encoder.s_vars) * 10}")
    if hasattr(original_encoder, 'sm_vars'):
        print(f"  - Mode vars (sm_j,m): ~{len(original_encoder.sm_vars) * 2}")
    if hasattr(original_encoder, 'x_vars'):
        print(f"  - Running vars (x_j,t,m): ~{sum(len(original_encoder.x_vars[j]) for j in original_encoder.x_vars) * 2}")

# 2. Block-based với các widths khác nhau
    block_results = {}

    if MRCPSPBlockBasedStaircase:
        widths = [5, 10, 15, 20, 30]

        for width in widths:
            print(f"\n" + "=" * 60)
            print(f"BLOCK-BASED STAIRCASE (width={width})")
            print("=" * 60)

            try:
                start_time = time.time()
                block_encoder = MRCPSPBlockBasedStaircase(reader, block_width=width)

                # Solve để generate constraints
                block_encoder.solve(makespan)

                block_time = time.time() - start_time

                block_results[width] = {
                    'variables': block_encoder.vpool.top if hasattr(block_encoder.vpool,
                                                                    'top') else block_encoder.vpool._top,
                    'clauses': len(block_encoder.cnf.clauses),
                    'time': block_time,
                    'register_bits': block_encoder.stats.get('register_bits', 0),
                    'amo_blocks': block_encoder.stats.get('amo_blocks', 0),
                    'amz_blocks': block_encoder.stats.get('amz_blocks', 0),
                    'connections': block_encoder.stats.get('connection_clauses', 0)
                }

                print(f"Variables: {block_results[width]['variables']}")
                print(f"Clauses: {block_results[width]['clauses']}")
                print(f"Register bits: {block_results[width]['register_bits']}")
                print(f"AMO blocks: {block_results[width]['amo_blocks']}")
                print(f"AMZ blocks: {block_results[width]['amz_blocks']}")
                print(f"Connection clauses: {block_results[width]['connections']}")
                print(f"Encoding time: {block_results[width]['time']:.3f}s")

            except Exception as e:
                print(f"Error with width {width}: {e}")
                traceback.print_exc()



def main():
    test_file = "data/j10/j102_2.mm"
    # Filter available files

    compare_original_vs_blockbased(test_file)

if __name__ == "__main__":
    main()
