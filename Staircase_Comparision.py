"""
So sánh Block-based Staircase với Standard Staircase cho MRCPSP
"""


def compare_encodings_detailed(instance_file):
    """So sánh chi tiết 2 phương pháp encoding"""

    import sys
    sys.path.append('.')

    # Import các encoders
    from No_Cloud_MRCPSP_G42_600s_1 import MRCPSPSATEncoder
    from MRCPSP_SCAMO import MRCPSPBlockBasedStaircase

    try:
        from MRCPSP_Basic import MRCPSPDataReader
    except:
        print("Cannot import MRCPSPDataReader")
        return

    # Read instance
    reader = MRCPSPDataReader(instance_file)

    print("=" * 100)
    print("SO SÁNH BLOCK-BASED vs STANDARD STAIRCASE")
    print("=" * 100)
    print(f"\nInstance: {instance_file}")
    print(f"Jobs: {reader.data['num_jobs']}")
    print(f"Horizon: {reader.get_horizon()}")

    # Test makespan
    test_makespan = reader.get_horizon() // 2

    # 1. Standard Staircase
    print("\n" + "=" * 60)
    print("STANDARD STAIRCASE ENCODING")
    print("=" * 60)

    standard_encoder = MRCPSPSATEncoder(reader)
    standard_encoder.solve(test_makespan)

    standard_stats = {
        'variables': standard_encoder.vpool.top,
        'clauses': len(standard_encoder.cnf.clauses),
    }

    # 2. Block-based với các widths khác nhau
    block_results = {}
    widths = [5, 10, 15, 20]

    for width in widths:
        print(f"\n" + "=" * 60)
        print(f"BLOCK-BASED STAIRCASE (width={width})")
        print("=" * 60)

        block_encoder = MRCPSPBlockBasedStaircase(reader, block_width=width)
        block_encoder.solve(test_makespan)

        block_results[width] = {
            'variables': block_encoder.vpool.top,
            'clauses': len(block_encoder.cnf.clauses),
            'register_bits': block_encoder.stats['register_bits'],
            'amo_blocks': block_encoder.stats['amo_blocks'],
            'amz_blocks': block_encoder.stats['amz_blocks'],
            'connections': block_encoder.stats['connection_clauses']
        }

    # 3. Comparison table
    print("\n" + "=" * 100)
    print("BẢNG SO SÁNH")
    print("=" * 100)

    print(f"\n{'Method':<25} {'Variables':<15} {'Clauses':<15} {'Registers':<15} {'Other':<30}")
    print("-" * 100)

    # Standard
    print(f"{'Standard Staircase':<25} {standard_stats['variables']:<15} ")

    # Block-based
    for width in widths:
        stats = block_results[width]
        other_info = f"AMO:{stats['amo_blocks']} AMZ:{stats['amz_blocks']} Conn:{stats['connections']}"
        print(f"{'Block-based (w=' + str(width) + ')':<25} {stats['variables']:<15} "
              f"{stats['clauses']:<15} {stats['register_bits']:<15} "
              f"{other_info:<30}")

    # 4. Analysis
    print("\n" + "=" * 100)
    print("PHÂN TÍCH")
    print("=" * 100)

    best_width = min(block_results.keys(),
                     key=lambda w: block_results[w]['clauses'])

    print(f"\n1. Block width tốt nhất: {best_width}")
    print(f"   - Clauses: {block_results[best_width]['clauses']}")
    print(f"   - So với Standard: {block_results[best_width]['clauses'] - standard_stats['clauses']:+d}")

    print(f"\n2. Trade-offs:")
    print(f"   - Width nhỏ: Nhiều blocks nhưng flexible hơn")
    print(f"   - Width lớn: Ít blocks nhưng có thể tạo clauses thừa")

    print(f"\n3. Memory usage:")

    return standard_stats, block_results


def analyze_block_structure(reader, job, block_width):
    """Phân tích cấu trúc block cho một job cụ thể"""

    print(f"\n{'=' * 60}")
    print(f"PHÂN TÍCH BLOCK STRUCTURE CHO JOB {job}")
    print(f"{'=' * 60}")

    from MRCPSP_SCAMO import MRCPSPBlockBasedStaircase

    encoder = MRCPSPBlockBasedStaircase(reader, block_width=block_width)
    encoder.calculate_time_windows()

    print(f"Time window: [{encoder.ES[job]}, {encoder.LS[job]}]")
    print(f"Window size: {encoder.LS[job] - encoder.ES[job] + 1}")
    print(f"Block width: {block_width}")

    # Tạo blocks
    blocks = encoder.create_blocks_for_job(job)

    print(f"\nBlocks được tạo:")
    for block_id, start, end, block_type in blocks:
        print(f"  Block {block_id}: [{start}, {end}) - Type: {block_type} - Size: {end - start}")

    print(f"\nTổng số blocks: {len(blocks)}")
    print(f"  - AMO blocks: {sum(1 for b in blocks if b[3] == 'AMO')}")
    print(f"  - AMZ blocks: {sum(1 for b in blocks if b[3] == 'AMZ')}")

    # Estimate clauses
    total_clauses = 0
    for _, start, end, block_type in blocks:
        size = end - start
        if size > 1:
            if block_type == 'AMO':
                # 4 formulas cho AMO
                total_clauses += 4 * (size - 1)
            else:  # AMZ
                # 3 formulas cho AMZ
                total_clauses += 3 * (size - 1)

    # Connection clauses
    amo_blocks = [b for b in blocks if b[3] == 'AMO']
    connection_clauses = (len(amo_blocks) - 1) * (block_width - 1)

    print(f"\nEstimated clauses:")
    print(f"  - Block clauses: {total_clauses}")
    print(f"  - Connection clauses: {connection_clauses}")
    print(f"  - Total: {total_clauses + connection_clauses}")


def main():
    """Main test function"""

    # Test instance
    test_file = "data/j10/j102_2.mm"

    # 1. So sánh encodings
    results = compare_encodings_detailed(test_file)

    # 2. Phân tích block structure cho vài jobs
    try:
        from MRCPSP_Basic import MRCPSPDataReader
        reader = MRCPSPDataReader(test_file)

        print("\n" + "=" * 100)
        print("PHÂN TÍCH BLOCK STRUCTURE")
        print("=" * 100)

        # Analyze cho vài jobs với block width khác nhau
        test_jobs = [2, 5, 8]
        test_widths = [5, 10, 15]

        for job in test_jobs:
            for width in test_widths:
                analyze_block_structure(reader, job, width)

    except Exception as e:
        print(f"Error in block analysis: {e}")


if __name__ == "__main__":
    main()