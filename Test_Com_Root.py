"""
So sánh Original Implementation với Block-based Staircase cho MRCPSP
"""

import time
import traceback


def compare_original_vs_blockbased(instance_file):
    """So sánh chi tiết giữa Original và Block-based encoding"""

    # Import các encoders
    from MRCPSP_Basic import MRCPSPDataReader, MRCPSPSATEncoder as OriginalEncoder

    try:
        from MRCPSP_SCAMO import MRCPSPBlockBasedStaircase
    except ImportError:
        print("Warning: Cannot import MRCPSPBlockBasedStaircase")
        print("Make sure MRCPSP_SCAMO.py exists in the same directory")
        MRCPSPBlockBasedStaircase = None

    # Read instance
    reader = MRCPSPDataReader(instance_file)

    print("=" * 100)
    print("SO SÁNH ORIGINAL IMPLEMENTATION vs BLOCK-BASED STAIRCASE")
    print("=" * 100)
    print(f"\nInstance: {instance_file}")
    print(f"Jobs: {reader.data['num_jobs']}")
    print(f"Horizon: {reader.get_horizon()}")
    print(f"Renewable resources: {reader.data['renewable_capacity']}")
    print(f"Non-renewable resources: {reader.data['nonrenewable_capacity']}")

    # Test makespan (use middle value for testing)
    test_makespan = reader.get_horizon() // 2
    print(f"\nTest makespan: {test_makespan}")

    # 1. Original Implementation
    print("\n" + "=" * 60)
    print("ORIGINAL IMPLEMENTATION (MRCPSPTest.py)")
    print("=" * 60)

    start_time = time.time()
    original_encoder = OriginalEncoder(reader)

    # Create variables and constraints
    original_encoder.cnf.clauses = []  # Reset
    # Try different ways to reset and access variable pool
    if hasattr(original_encoder.vpool, '_top'):
        original_encoder.vpool._top = 0  # Reset variable pool
    elif hasattr(original_encoder.vpool, 'top'):
        original_encoder.vpool.top = 0

    original_encoder.create_variables()
    original_encoder.add_start_time_constraints()
    original_encoder.add_mode_selection_constraints()
    original_encoder.add_precedence_constraints()
    original_encoder.add_running_variable_constraints()
    original_encoder.add_renewable_resource_constraints()
    original_encoder.add_nonrenewable_resource_constraints()
    original_encoder.add_makespan_constraint(test_makespan)

    original_time = time.time() - start_time

    # Get variable count - try different attributes
    var_count = 0
    if hasattr(original_encoder.vpool, '_top'):
        var_count = original_encoder.vpool._top
    elif hasattr(original_encoder.vpool, 'top'):
        var_count = original_encoder.vpool.top
    elif hasattr(original_encoder, 'var_counter'):
        var_count = original_encoder.var_counter
    else:
        # Estimate from variable dictionaries if available
        if hasattr(original_encoder, 's_vars') and hasattr(original_encoder, 'sm_vars') and hasattr(original_encoder,
                                                                                                    'x_vars'):
            s_count = sum(len(original_encoder.s_vars.get(j, {})) for j in original_encoder.s_vars)
            sm_count = sum(len(original_encoder.sm_vars.get(j, {})) for j in original_encoder.sm_vars)
            x_count = sum(
                sum(len(original_encoder.x_vars.get(j, {}).get(t, {})) for t in original_encoder.x_vars.get(j, {})) for
                j in original_encoder.x_vars)
            var_count = s_count + sm_count + x_count

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
        print(
            f"  - Running vars (x_j,t,m): ~{sum(len(original_encoder.x_vars[j]) for j in original_encoder.x_vars) * 2}")

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
                block_encoder.solve(test_makespan)

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

    # 3. Comparison table
    print("\n" + "=" * 100)
    print("BẢNG SO SÁNH TỔNG HỢP")
    print("=" * 100)

    print(f"\n{'Method':<30} {'Variables':<12} {'Clauses':<12} {'Time (s)':<10} {'Reduction':<15}")
    print("-" * 90)

    # Original
    print(f"{'Original (MRCPSPTest.py)':<30} {original_stats['variables']:<12} "
          f"{original_stats['clauses']:<12} {original_stats['time']:<10.3f} {'(baseline)':<15}")

    # Block-based
    for width in sorted(block_results.keys()):
        stats = block_results[width]
        clause_reduction = ((original_stats['clauses'] - stats['clauses']) / original_stats['clauses'] * 100)

        # Handle division by zero for variables
        if original_stats['variables'] > 0:
            var_reduction = ((original_stats['variables'] - stats['variables']) / original_stats['variables'] * 100)
            reduction_text = f"C:{clause_reduction:+.1f}% V:{var_reduction:+.1f}%"
        else:
            reduction_text = f"C:{clause_reduction:+.1f}% V:N/A"

        print(f"{'Block-based (w=' + str(width) + ')':<30} {stats['variables']:<12} "
              f"{stats['clauses']:<12} {stats['time']:<10.3f} "
              f"{reduction_text}")

    # 4. Detailed Analysis
    print("\n" + "=" * 100)
    print("PHÂN TÍCH CHI TIẾT")
    print("=" * 100)

    if block_results:
        # Find best configuration
        best_clause_width = min(block_results.keys(),
                                key=lambda w: block_results[w]['clauses'])
        best_var_width = min(block_results.keys(),
                             key=lambda w: block_results[w]['variables'])

        print(f"\n1. Cấu hình tốt nhất:")
        print(f"   - Ít clauses nhất: width={best_clause_width}")
        print(f"     + Clauses: {block_results[best_clause_width]['clauses']} "
              f"(giảm {original_stats['clauses'] - block_results[best_clause_width]['clauses']} "
              f"= {(original_stats['clauses'] - block_results[best_clause_width]['clauses']) / original_stats['clauses'] * 100:.1f}%)")

        print(f"   - Ít variables nhất: width={best_var_width}")
        if original_stats['variables'] > 0:
            print(f"     + Variables: {block_results[best_var_width]['variables']} "
                  f"(giảm {original_stats['variables'] - block_results[best_var_width]['variables']} "
                  f"= {(original_stats['variables'] - block_results[best_var_width]['variables']) / original_stats['variables'] * 100:.1f}%)")
        else:
            print(f"     + Variables: {block_results[best_var_width]['variables']} (original count unavailable)")

        print(f"\n2. Trade-offs theo block width:")
        for width in sorted(block_results.keys()):
            stats = block_results[width]
            print(f"   Width {width:2d}: {stats['amo_blocks']:3d} AMO + {stats['amz_blocks']:3d} AMZ blocks, "
                  f"{stats['connections']:4d} connections")

        print(f"\n3. Hiệu suất encoding:")
        fastest = min(block_results.keys(), key=lambda w: block_results[w]['time'])
        print(f"   - Original: {original_stats['time']:.3f}s")
        print(f"   - Fastest block-based: width={fastest} ({block_results[fastest]['time']:.3f}s)")

    return original_stats, block_results

def analyze_scaling(instance_files):
    """Phân tích scaling trên nhiều instances"""

    print("\n" + "=" * 100)
    print("PHÂN TÍCH SCALING TRÊN NHIỀU INSTANCES")
    print("=" * 100)

    results = []

    for instance_file in instance_files:
        try:
            print(f"\n\nProcessing: {instance_file}")
            print("-" * 50)

            original, block = compare_original_vs_blockbased(instance_file)

            # Get best block configuration
            if block:
                best_width = min(block.keys(), key=lambda w: block[w]['clauses'])
                results.append({
                    'instance': instance_file,
                    'original_vars': original['variables'],
                    'original_clauses': original['clauses'],
                    'best_block_vars': block[best_width]['variables'],
                    'best_block_clauses': block[best_width]['clauses'],
                    'best_width': best_width,
                    'clause_reduction': (original['clauses'] - block[best_width]['clauses']) / original['clauses'] * 100
                })

        except Exception as e:
            print(f"Error processing {instance_file}: {e}")

    # Summary table
    if results:
        print("\n" + "=" * 100)
        print("TỔNG KẾT SCALING")
        print("=" * 100)

        print(f"\n{'Instance':<30} {'Orig Clauses':<15} {'Best Block':<15} {'Reduction':<12} {'Best Width':<10}")
        print("-" * 90)

        for r in results:
            print(f"{r['instance']:<30} {r['original_clauses']:<15} "
                  f"{r['best_block_clauses']:<15} {r['clause_reduction']:>10.1f}% "
                  f"{r['best_width']:<10}")

        avg_reduction = sum(r['clause_reduction'] for r in results) / len(results)
        print(f"\nAverage clause reduction: {avg_reduction:.1f}%")


def main():
    """Main test function"""

    # Test single instance
    test_file = "data/j10/j102_2.mm"

    print("TESTING SINGLE INSTANCE")
    original_stats, block_stats = compare_original_vs_blockbased(test_file)

    # Test multiple instances if available
    test_instances = [
        "data/j10/j102_1.mm",
        "data/j10/j102_2.mm",
        "data/j10/j102_3.mm",
        "data/j10/j102_4.mm",
        "data/j10/j102_5.mm"
    ]

    # Filter available files
    import os
    available_instances = [f for f in test_instances if os.path.exists(f)]

    if len(available_instances) > 1:
        analyze_scaling(available_instances[:3])  # Test with first 3 instances


if __name__ == "__main__":
    main()