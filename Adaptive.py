"""
Adaptive Block-based Staircase với độ rộng block động
Dựa theo bài báo: độ rộng block phụ thuộc vào sequence của biến
"""

import math
from MRCPSTest import MRCPSPDataReader


class AdaptiveBlockWidth:
    """
    Tính toán độ rộng block tự động dựa trên đặc điểm của sequence
    """

    def __init__(self, reader):
        self.reader = reader
        self.data = reader.data
        self.jobs = reader.data['num_jobs']
        self.horizon = reader.get_horizon()

        # Calculate time windows
        self.calculate_time_windows()

    def calculate_time_windows(self):
        """Tính ES và LS cho mỗi job"""
        self.ES = {}
        self.LS = {}

        # Initialize
        for j in range(1, self.jobs + 1):
            self.ES[j] = 0
            self.LS[j] = self.horizon

        # Forward pass for ES
        self.ES[1] = 0

        def calc_es(j):
            if j in self.ES and self.ES[j] > 0:
                return self.ES[j]

            max_pred_finish = 0
            for pred in range(1, self.jobs + 1):
                if pred in self.data['precedence'] and j in self.data['precedence'][pred]:
                    pred_es = calc_es(pred)
                    min_duration = min(mode[0] for mode in self.data['job_modes'][pred])
                    max_pred_finish = max(max_pred_finish, pred_es + min_duration)

            self.ES[j] = max_pred_finish
            return self.ES[j]

        for j in range(1, self.jobs + 1):
            calc_es(j)

        # Backward pass for LS
        for j in range(1, self.jobs + 1):
            if j in self.data['job_modes'] and self.data['job_modes'][j]:
                max_duration = max(mode[0] for mode in self.data['job_modes'][j])
                self.LS[j] = self.horizon - max_duration

    def get_adaptive_width_for_job(self, job_id):
        """
        Tính độ rộng block thích hợp cho một job cụ thể
        Dựa trên:
        1. Kích thước time window
        2. Số lượng modes
        3. Độ phức tạp precedence
        """

        # 1. Time window size
        window_size = self.LS[job_id] - self.ES[job_id] + 1

        # 2. Number of modes
        num_modes = len(self.data['job_modes'][job_id])

        # 3. Precedence complexity (số predecessors và successors)
        num_predecessors = 0
        num_successors = 0

        # Count predecessors
        for pred in range(1, self.jobs + 1):
            if pred in self.data['precedence'] and job_id in self.data['precedence'][pred]:
                num_predecessors += 1

        # Count successors
        if job_id in self.data['precedence']:
            num_successors = len(self.data['precedence'][job_id])

        precedence_complexity = num_predecessors + num_successors

        # 4. Calculate adaptive width
        # Công thức heuristic: cân bằng giữa số blocks và flexibility

        if window_size <= 10:
            # Small window: use small blocks for flexibility
            base_width = 3
        elif window_size <= 30:
            # Medium window: moderate block size
            base_width = int(math.sqrt(window_size))
        else:
            # Large window: larger blocks to reduce total blocks
            base_width = int(window_size / 10) + 5

        # Adjust based on modes
        if num_modes > 3:
            # More modes need more flexibility
            base_width = max(3, base_width - 1)

        # Adjust based on precedence
        if precedence_complexity > 5:
            # Complex precedence needs smaller blocks
            base_width = max(3, base_width - 1)
        elif precedence_complexity < 2:
            # Simple precedence can use larger blocks
            base_width = base_width + 2

        # Ensure reasonable bounds
        base_width = max(3, min(base_width, 20))

        return base_width

    def get_adaptive_widths_all_jobs(self):
        """
        Tính độ rộng block cho tất cả jobs
        Trả về dictionary {job_id: width}
        """
        widths = {}
        for j in range(1, self.jobs + 1):
            widths[j] = self.get_adaptive_width_for_job(j)
        return widths

    def get_global_adaptive_width(self):
        """
        Tính một độ rộng block chung tối ưu cho toàn bộ instance
        """
        all_widths = []

        for j in range(1, self.jobs + 1):
            window_size = self.LS[j] - self.ES[j] + 1
            if window_size > 0:
                all_widths.append(window_size)

        if not all_widths:
            return 10  # Default

        # Use statistical approach
        avg_window = sum(all_widths) / len(all_widths)
        median_window = sorted(all_widths)[len(all_widths) // 2]

        # Heuristic formula
        if avg_window <= 15:
            optimal_width = 5
        elif avg_window <= 30:
            optimal_width = int(math.sqrt(median_window))
        else:
            optimal_width = int(median_window / 8) + 3

        # Consider instance size
        if self.jobs <= 10:
            # Small instance: smaller blocks
            optimal_width = max(4, optimal_width - 1)
        elif self.jobs >= 30:
            # Large instance: larger blocks
            optimal_width = min(20, optimal_width + 2)

        return max(4, min(optimal_width, 25))

    def analyze_sequence_pattern(self, job_id):
        """
        Phân tích pattern của sequence để tối ưu block structure
        Trả về suggested block boundaries
        """
        window_start = self.ES[job_id]
        window_end = self.LS[job_id]
        window_size = window_end - window_start + 1

        # Analyze precedence structure
        critical_points = set()

        # Add points where predecessors complete
        for pred in range(1, self.jobs + 1):
            if pred in self.data['precedence'] and job_id in self.data['precedence'][pred]:
                if pred in self.data['job_modes']:
                    for mode in self.data['job_modes'][pred]:
                        completion = self.ES[pred] + mode[0]
                        if window_start <= completion <= window_end:
                            critical_points.add(completion)

        # Add points where successors must start
        if job_id in self.data['precedence']:
            for succ in self.data['precedence'][job_id]:
                latest_start = self.LS[succ]
                if window_start <= latest_start <= window_end:
                    critical_points.add(latest_start)

        # Convert to sorted list
        critical_points = sorted(list(critical_points))

        # Create block boundaries based on critical points
        if not critical_points:
            # No critical points: use uniform blocks
            width = self.get_adaptive_width_for_job(job_id)
            boundaries = list(range(window_start, window_end + 1, width))
            if boundaries[-1] < window_end:
                boundaries.append(window_end + 1)
        else:
            # Use critical points to guide block boundaries
            boundaries = [window_start]

            for point in critical_points:
                if point - boundaries[-1] >= 3:  # Minimum block size
                    boundaries.append(point)

            if window_end + 1 - boundaries[-1] >= 3:
                boundaries.append(window_end + 1)
            else:
                boundaries[-1] = window_end + 1

        return boundaries


def compare_adaptive_vs_fixed(instance_file):
    """
    So sánh Adaptive Block Width với Fixed Block Width
    """

    from MRCPSTest import MRCPSPSATEncoder as OriginalEncoder

    print("=" * 100)
    print("SO SÁNH ADAPTIVE vs FIXED BLOCK WIDTH")
    print("=" * 100)

    # Read instance
    reader = MRCPSPDataReader(instance_file)

    print(f"\nInstance: {instance_file}")
    print(f"Jobs: {reader.data['num_jobs']}")
    print(f"Horizon: {reader.get_horizon()}")

    # Calculate adaptive widths
    adaptive = AdaptiveBlockWidth(reader)

    # 1. Analyze adaptive widths for each job
    print("\n" + "=" * 60)
    print("ADAPTIVE WIDTH ANALYSIS")
    print("=" * 60)

    job_widths = adaptive.get_adaptive_widths_all_jobs()
    global_width = adaptive.get_global_adaptive_width()

    print(f"\nGlobal optimal width: {global_width}")
    print(f"\nPer-job adaptive widths:")
    print(f"{'Job':<5} {'ES':<5} {'LS':<5} {'Window':<8} {'Modes':<7} {'Width':<7}")
    print("-" * 45)

    for j in range(1, min(11, reader.data['num_jobs'] + 1)):  # Show first 10 jobs
        window_size = adaptive.LS[j] - adaptive.ES[j] + 1
        num_modes = len(reader.data['job_modes'][j])
        print(f"{j:<5} {adaptive.ES[j]:<5} {adaptive.LS[j]:<5} "
              f"{window_size:<8} {num_modes:<7} {job_widths[j]:<7}")

    # 2. Analyze sequence patterns
    print("\n" + "=" * 60)
    print("SEQUENCE PATTERN ANALYSIS")
    print("=" * 60)

    # Analyze a few representative jobs
    test_jobs = [2, reader.data['num_jobs'] // 2, reader.data['num_jobs'] - 1]

    for job in test_jobs:
        if job <= reader.data['num_jobs']:
            print(f"\nJob {job}:")
            boundaries = adaptive.analyze_sequence_pattern(job)
            print(f"  Suggested block boundaries: {boundaries}")

            if len(boundaries) > 1:
                block_sizes = [boundaries[i + 1] - boundaries[i]
                               for i in range(len(boundaries) - 1)]
                print(f"  Block sizes: {block_sizes}")
                print(f"  Average block size: {sum(block_sizes) / len(block_sizes):.1f}")

    # 3. Statistics
    print("\n" + "=" * 60)
    print("STATISTICS")
    print("=" * 60)

    width_distribution = {}
    for w in job_widths.values():
        width_distribution[w] = width_distribution.get(w, 0) + 1

    print("\nWidth distribution:")
    for w in sorted(width_distribution.keys()):
        print(f"  Width {w:2d}: {width_distribution[w]:3d} jobs "
              f"({'#' * min(50, width_distribution[w])})")

    avg_width = sum(job_widths.values()) / len(job_widths)
    print(f"\nAverage adaptive width: {avg_width:.1f}")
    print(f"Min width: {min(job_widths.values())}")
    print(f"Max width: {max(job_widths.values())}")

    # 4. Comparison with fixed widths
    print("\n" + "=" * 60)
    print("COMPARISON WITH FIXED WIDTHS")
    print("=" * 60)

    fixed_widths = [5, 10, 15, 20, global_width]

    print(f"\n{'Strategy':<30} {'Description':<50}")
    print("-" * 80)
    print(f"{'Fixed width=5':<30} {'Small blocks, high flexibility':<50}")
    print(f"{'Fixed width=10':<30} {'Medium blocks, balanced':<50}")
    print(f"{'Fixed width=15':<30} {'Large blocks, fewer connections':<50}")
    print(f"{'Fixed width=20':<30} {'Very large blocks, minimal connections':<50}")
    print(f"{f'Adaptive global={global_width}':<30} {'Optimized for this instance':<50}")
    print(f"{'Adaptive per-job':<30} {'Custom width for each job based on its properties':<50}")

    return job_widths, global_width


def test_adaptive_encoding(instance_file, use_adaptive=True):
    """
    Test encoding với adaptive width
    """

    reader = MRCPSPDataReader(instance_file)
    adaptive = AdaptiveBlockWidth(reader)

    if use_adaptive:
        # Use adaptive width
        optimal_width = adaptive.get_global_adaptive_width()
        print(f"\nUsing adaptive width: {optimal_width}")
    else:
        # Use fixed width
        optimal_width = 10
        print(f"\nUsing fixed width: {optimal_width}")

    # Here you would call your Block-based encoder with the optimal width
    # block_encoder = MRCPSPBlockBasedStaircase(reader, block_width=optimal_width)

    return optimal_width


def main():
    """Main test function"""

    # Test instance
    test_file = "data/j10/j1014_8.mm"

    print("ADAPTIVE BLOCK WIDTH ANALYSIS")
    print("=" * 100)

    # Analyze adaptive widths
    job_widths, global_width = compare_adaptive_vs_fixed(test_file)

    # Test encoding
    print("\n" + "=" * 100)
    print("TESTING ADAPTIVE ENCODING")
    print("=" * 100)

    adaptive_width = test_adaptive_encoding(test_file, use_adaptive=True)
    fixed_width = test_adaptive_encoding(test_file, use_adaptive=False)

    print(f"\nRecommendation:")
    print(f"- For this instance, use global adaptive width = {global_width}")
    print(f"- This balances between clause reduction and encoding complexity")
    print(f"- For more fine-grained optimization, consider per-job adaptive widths")


if __name__ == "__main__":
    main()