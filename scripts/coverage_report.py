#!/usr/bin/env python3

"""
Analyse lcov coverage data and report gaps.

Reads an lcov .info file and summarises, for the sources in src/ and
jbmc/src/:
  1. the coverage of each module (directory), worst first;
  2. the files with 0% coverage (with at least --zero-min-lines lines);
  3. the files with less than --low-threshold percent coverage (with at least
     --low-min-lines lines).

Usage, from the repository root (or see --base-dir)::

    # After running the coverage build:
    python3 scripts/coverage_report.py build/html/coverage.info

    # Markdown output for CI job summaries:
    python3 scripts/coverage_report.py --markdown build/html/coverage.info

    # Customise thresholds:
    python3 scripts/coverage_report.py --zero-min-lines 10 --low-threshold 30 \
        build/html/coverage.info
"""

import argparse
import os
import sys
from collections import defaultdict

# Paths below src/ or jbmc/src/ that are not CBMC's own sources.
EXCLUDED = ("minisat", "miniz", "lex.yy.", ".tab.cpp", ".tab.h")


def parse_lcov(info_path):
    """Return {source file: {line number: hit count}}.

    A file may have several records (one per test name), whose counts are
    added up."""
    coverage = defaultdict(lambda: defaultdict(int))
    current = None
    with open(info_path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("SF:"):
                current = coverage[line[3:]]
            elif line.startswith("DA:") and current is not None:
                fields = line[3:].split(",")
                if len(fields) >= 2:
                    current[int(fields[0])] += int(fields[1])
            elif line == "end_of_record":
                current = None
    return coverage


def source_files(coverage, base_dir):
    """Return {path relative to base_dir: (lines hit, lines total)} for the
    files in src/ and jbmc/src/ below base_dir."""
    prefix = base_dir.rstrip("/") + "/"
    result = {}
    for path, lines in coverage.items():
        if not path.startswith(prefix):
            continue
        rel = path[len(prefix):]
        if not rel.startswith(("src/", "jbmc/src/")):
            continue
        if any(excluded in rel for excluded in EXCLUDED):
            continue
        hit = sum(1 for count in lines.values() if count > 0)
        result[rel] = (hit, len(lines))
    return result


def module_of(path):
    """The directory below src/ or jbmc/src/ that contains a source file, e.g.
    src/goto-programs/foo.cpp -> src/goto-programs."""
    parts = path.split("/")
    depth = 3 if parts[0] == "jbmc" else 2
    return "/".join(parts[:depth])


def percentage(hit, total):
    return hit / total * 100 if total else 0.0


def analyse(files, args):
    modules = defaultdict(lambda: [0, 0])
    for path, (hit, total) in files.items():
        modules[module_of(path)][0] += hit
        modules[module_of(path)][1] += total
    modules = sorted(
        ((m, h, t) for m, (h, t) in modules.items() if t > 0),
        key=lambda m: (percentage(m[1], m[2]), m[0]))
    zero = sorted(
        ((p, t) for p, (h, t) in files.items()
         if h == 0 and t >= args.zero_min_lines),
        key=lambda f: (-f[1], f[0]))
    low = sorted(
        ((p, h, t) for p, (h, t) in files.items()
         if h > 0 and t >= args.low_min_lines
         and percentage(h, t) < args.low_threshold),
        key=lambda f: (percentage(f[1], f[2]), f[0]))
    hit = sum(h for h, _ in files.values())
    total = sum(t for _, t in files.values())
    return hit, total, modules, zero, low


def print_report(files, args):
    hit, total, modules, zero, low = analyse(files, args)

    def table(header, rows):
        if args.markdown:
            print("| " + " | ".join(header) + " |")
            print("|" + "|".join("---" for _ in header) + "|")
            for row in rows:
                print("| " + " | ".join(str(c) for c in row) + " |")
        else:
            widths = [max(len(str(c)) for c in col)
                      for col in zip(header, *rows)]
            for row in [header] + rows:
                print("  ".join(str(c).ljust(w) if i == 0 else str(c).rjust(w)
                                for i, (c, w) in enumerate(zip(row, widths))))
        print()

    def heading(text):
        print(("## " if args.markdown else "") + text + "\n")

    if args.markdown:
        print("# Coverage Gap Report\n")
    print(f"Overall source coverage: {percentage(hit, total):.1f}%"
          f" ({hit}/{total} lines)\n")

    heading("Coverage per module, worst first")
    table(["Module", "Coverage", "Lines", "Missed"],
          [[m, f"{percentage(h, t):.1f}%", t, t - h] for m, h, t in modules])

    if zero:
        heading(f"Files of at least {args.zero_min_lines} lines with 0%"
                f" coverage: {len(zero)}")
        table(["File", "Lines"], [[p, t] for p, t in zero])

    if low:
        heading(f"Files of at least {args.low_min_lines} lines with less"
                f" than {args.low_threshold:g}% coverage: {len(low)}")
        table(["File", "Coverage", "Lines", "Missed"],
              [[p, f"{percentage(h, t):.1f}%", t, t - h] for p, h, t in low])


def main():
    parser = argparse.ArgumentParser(
        description="Analyse lcov coverage data and report gaps")
    parser.add_argument("info_file", help="Path to lcov .info file")
    parser.add_argument(
        "--base-dir",
        default=os.getcwd(),
        help="Repository root (default: the current directory)")
    parser.add_argument(
        "--zero-min-lines", type=int, default=20,
        help="Minimum lines for a 0%% file to be reported (default: 20)")
    parser.add_argument(
        "--low-threshold", type=float, default=20,
        help="Coverage percentage threshold for 'low coverage' (default: 20)")
    parser.add_argument(
        "--low-min-lines", type=int, default=50,
        help="Minimum lines for a low-coverage file to be reported"
             " (default: 50)")
    parser.add_argument(
        "--markdown", action="store_true",
        help="Output Markdown (for CI job summaries)")
    args = parser.parse_args()

    coverage = parse_lcov(args.info_file)
    if not coverage:
        print(f"No coverage data found in {args.info_file}", file=sys.stderr)
        sys.exit(1)

    files = source_files(coverage, args.base_dir)
    if not files:
        print(f"No source files below {args.base_dir}/src or"
              f" {args.base_dir}/jbmc/src (see --base-dir)", file=sys.stderr)
        sys.exit(1)

    print_report(files, args)


if __name__ == "__main__":
    main()
