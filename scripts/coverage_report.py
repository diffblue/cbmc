#!/usr/bin/env python3

"""
Analyse lcov coverage data and report gaps.

Reads an lcov .info file and produces a summary of:
  1. Per-module coverage (sorted worst-first)
  2. Files with 0% coverage (above a minimum line threshold)
  3. Files with very low coverage (<20%, above a minimum line threshold)

Usage::

    # After running the coverage build:
    python3 scripts/coverage_report.py build/html/coverage.info

    # Markdown output for CI job summaries:
    python3 scripts/coverage_report.py --markdown build/html/coverage.info

    # Customise thresholds:
    python3 scripts/coverage_report.py --zero-min-lines 10 --low-threshold 30 \
        build/html/coverage.info
"""

import argparse
import sys
from collections import defaultdict
from pathlib import Path


def parse_lcov(info_path: str) -> dict[str, tuple[int, int]]:
    """Parse an lcov .info file, returning {filepath: (lines_hit, lines_total)}."""
    coverage: dict[str, tuple[int, int]] = {}
    current_file = None
    hit = total = 0

    with open(info_path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("SF:"):
                current_file = line[3:]
                hit = total = 0
            elif line.startswith("DA:"):
                parts = line[3:].split(",")
                if len(parts) >= 2:
                    total += 1
                    if int(parts[1]) > 0:
                        hit += 1
            elif line == "end_of_record" and current_file:
                coverage[current_file] = (hit, total)
                current_file = None

    return coverage


def filter_source_files(
    coverage: dict[str, tuple[int, int]], base_dir: str
) -> dict[str, tuple[int, int]]:
    """Keep only src/ and jbmc/src/ files, excluding tests and third-party."""
    result = {}
    for path, stats in coverage.items():
        rel = path.replace(base_dir + "/", "") if path.startswith(base_dir) else path
        if not (rel.startswith("src/") or rel.startswith("jbmc/src/")):
            continue
        if any(
            skip in rel
            for skip in (
                "/unit/",
                "minisat",
                "miniz",
                "/catch/",
                "/testing-utils/",
                "lex.yy.",
                ".tab.cpp",
            )
        ):
            continue
        result[rel] = stats
    return result


def module_of(path: str) -> str:
    """Extract the module directory from a source path.

    Groups files by their containing directory under src/ or jbmc/src/,
    e.g. ``src/goto-programs/foo.cpp`` -> ``src/goto-programs``.
    """
    parts = path.split("/")
    # jbmc/src/module/... -> jbmc/src/module
    if len(parts) >= 3 and parts[0] == "jbmc":
        return "/".join(parts[:3])
    # src/module/... -> src/module
    if len(parts) >= 2:
        return "/".join(parts[:2])
    return parts[0]


def fmt_pct(hit: int, total: int) -> str:
    if total == 0:
        return "  n/a"
    return f"{hit / total * 100:5.1f}%"


def print_text_report(
    src_files: dict[str, tuple[int, int]],
    zero_min_lines: int,
    low_threshold: float,
    low_min_lines: int,
) -> None:
    # Module summary
    dir_stats: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    for path, (hit, total) in src_files.items():
        mod = module_of(path)
        dir_stats[mod][0] += hit
        dir_stats[mod][1] += total

    total_hit = sum(h for h, _ in src_files.values())
    total_lines = sum(t for _, t in src_files.values())

    print(f"Overall source coverage: {fmt_pct(total_hit, total_lines)}"
          f"  ({total_hit}/{total_lines} lines)\n")

    print(f"{'Module':<55s} {'Coverage':>8s} {'Lines':>7s} {'Missed':>7s}")
    print("=" * 80)
    for mod, (h, t) in sorted(
        dir_stats.items(), key=lambda kv: kv[1][0] / max(kv[1][1], 1)
    ):
        print(f"{mod:<55s} {fmt_pct(h, t):>8s} {t:>7d} {t - h:>7d}")

    # 0% files
    zero_files = [
        (p, t) for p, (h, t) in src_files.items() if h == 0 and t >= zero_min_lines
    ]
    zero_files.sort(key=lambda x: -x[1])
    if zero_files:
        print(f"\n\nFiles with 0% coverage (>={zero_min_lines} lines):"
              f"  {len(zero_files)} files\n")
        print(f"{'File':<72s} {'Lines':>6s}")
        print("-" * 80)
        for path, total in zero_files:
            print(f"{path:<72s} {total:>6d}")

    # Low coverage files
    low_files = [
        (p, h, t)
        for p, (h, t) in src_files.items()
        if t >= low_min_lines and 0 < h / t < low_threshold / 100
    ]
    low_files.sort(key=lambda x: x[1] / x[2])
    if low_files:
        print(f"\n\nFiles with <{low_threshold:.0f}% coverage"
              f" (>={low_min_lines} lines):  {len(low_files)} files\n")
        print(f"{'File':<65s} {'Cov':>6s} {'Lines':>6s} {'Missed':>6s}")
        print("-" * 85)
        for path, h, t in low_files:
            print(f"{path:<65s} {fmt_pct(h, t):>6s} {t:>6d} {t - h:>6d}")


def print_markdown_report(
    src_files: dict[str, tuple[int, int]],
    zero_min_lines: int,
    low_threshold: float,
    low_min_lines: int,
) -> None:
    total_hit = sum(h for h, _ in src_files.values())
    total_lines = sum(t for _, t in src_files.values())

    print(f"# Coverage Gap Report\n")
    print(f"Overall source coverage: **{fmt_pct(total_hit, total_lines).strip()}**"
          f" ({total_hit}/{total_lines} lines)\n")

    # Module summary
    dir_stats: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    for path, (hit, total) in src_files.items():
        mod = module_of(path)
        dir_stats[mod][0] += hit
        dir_stats[mod][1] += total

    print("## Per-Module Coverage (worst first)\n")
    print("| Module | Coverage | Lines | Missed |")
    print("|--------|----------|-------|--------|")
    for mod, (h, t) in sorted(
        dir_stats.items(), key=lambda kv: kv[1][0] / max(kv[1][1], 1)
    ):
        if t - h < 10:
            continue
        print(f"| {mod} | {fmt_pct(h, t).strip()} | {t} | {t - h} |")

    # 0% files
    zero_files = [
        (p, t) for p, (h, t) in src_files.items() if h == 0 and t >= zero_min_lines
    ]
    zero_files.sort(key=lambda x: -x[1])
    if zero_files:
        print(f"\n## Files with 0% Coverage ({len(zero_files)} files,"
              f" >={zero_min_lines} lines)\n")
        print("| File | Lines |")
        print("|------|-------|")
        for path, total in zero_files:
            print(f"| {path} | {total} |")

    # Low coverage files
    low_files = [
        (p, h, t)
        for p, (h, t) in src_files.items()
        if t >= low_min_lines and 0 < h / t < low_threshold / 100
    ]
    low_files.sort(key=lambda x: x[1] / x[2])
    if low_files:
        print(f"\n## Files with <{low_threshold:.0f}% Coverage"
              f" ({len(low_files)} files, >={low_min_lines} lines)\n")
        print("| File | Coverage | Lines | Missed |")
        print("|------|----------|-------|--------|")
        for path, h, t in low_files:
            print(f"| {path} | {fmt_pct(h, t).strip()} | {t} | {t - h} |")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Analyse lcov coverage data and report gaps"
    )
    parser.add_argument("info_file", help="Path to lcov .info file")
    parser.add_argument(
        "--base-dir",
        default=None,
        help="Repository root (auto-detected from info file paths)",
    )
    parser.add_argument(
        "--zero-min-lines",
        type=int,
        default=20,
        help="Minimum lines for a 0%% file to be reported (default: 20)",
    )
    parser.add_argument(
        "--low-threshold",
        type=float,
        default=20,
        help="Coverage percentage threshold for 'low coverage' (default: 20)",
    )
    parser.add_argument(
        "--low-min-lines",
        type=int,
        default=50,
        help="Minimum lines for a low-coverage file to be reported (default: 50)",
    )
    parser.add_argument(
        "--markdown",
        action="store_true",
        help="Output Markdown (for CI job summaries)",
    )
    args = parser.parse_args()

    coverage = parse_lcov(args.info_file)
    if not coverage:
        print(f"No coverage data found in {args.info_file}", file=sys.stderr)
        sys.exit(1)

    # Auto-detect base dir from common path prefix
    base_dir = args.base_dir
    if base_dir is None:
        # Find repo root: look for a path containing /src/ that isn't a
        # build directory, then take the longest common prefix of all such
        # paths up to (but not including) the first /src/ or /jbmc/ segment.
        paths = [p for p in coverage if "/src/" in p and "/build" not in p]
        if paths:
            # Use os.path.commonpath for robustness
            import os

            base_dir = os.path.commonpath(paths)
            # Trim to the directory above src/ and jbmc/
            for marker in ("/src/", "/jbmc/"):
                idx = base_dir.find(marker)
                if idx != -1:
                    base_dir = base_dir[:idx]
                    break
        else:
            base_dir = ""

    src_files = filter_source_files(coverage, base_dir)
    if not src_files:
        print("No source files found after filtering", file=sys.stderr)
        sys.exit(1)

    if args.markdown:
        print_markdown_report(
            src_files, args.zero_min_lines, args.low_threshold, args.low_min_lines
        )
    else:
        print_text_report(
            src_files, args.zero_min_lines, args.low_threshold, args.low_min_lines
        )


if __name__ == "__main__":
    main()
