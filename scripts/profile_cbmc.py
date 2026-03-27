#!/usr/bin/env python3

"""CBMC Performance Profiling Tool

Profiles CBMC's pre-solver stages using perf and generates flamegraphs
with aggregated results across multiple benchmarks.

Usage:
  scripts/profile_cbmc.py [options] <input.c> [-- <cbmc-args>]
  scripts/profile_cbmc.py [options] --auto [-- <cbmc-args>]
  scripts/profile_cbmc.py --diff <ref-a> <ref-b> [-- <cbmc-args>]
  scripts/profile_cbmc.py --compare <dir-a> <dir-b> [--compare-labels A B]

Options:
  --build-dir DIR      CMake build directory (default: build)
  --output-dir DIR     Output directory for results (default: profile-results)
  --timeout SECS       Timeout per benchmark in seconds (default: 300)
  --memory-limit MB    Virtual memory limit in MB (default: 20480)
  --flamegraph-dir DIR Path to FlameGraph repo (auto-cloned if missing)
  --no-skip-solver     Include the SAT/SMT solver in profiling
  --auto               Generate and run built-in benchmarks (3 quick tests)
  --auto-large         Generate and run extended benchmark suite (10 tests)
  --auto-csmith        Generate benchmarks using CSmith with fixed seeds
  --debug-binary PATH  CBMC binary with debug info for source-level detail
  --diff REF_A REF_B   Differential profiling: compare two git refs
  --compare DIR_A DIR_B Compare two existing result directories
  --compare-labels A B  Labels for --compare (default: directory names)
  --runs N             Run each benchmark N times for statistical significance
  --help               Show this help

Outputs (per benchmark):
  perf.data            Raw perf recording
  flamegraph.svg       Interactive flamegraph

Outputs (aggregated):
  summary.txt          Text summary with optimization suggestions
  aggregated.svg       Combined flamegraph across all benchmarks
  results.json         Machine-readable results

Source-level call site resolution:
  For source file:line information in the hotspot analysis, build a
  separate binary with debug info and pass it via --debug-binary:

    cmake -S . -Bbuild-debug -DCMAKE_BUILD_TYPE=RelWithDebInfo -DWITH_JBMC=OFF
    cmake --build build-debug --target cbmc -j$(nproc)
    scripts/profile_cbmc.py --auto --debug-binary build-debug/bin/cbmc

  Profiling is done with the fast Release build; the debug binary is only
  used post-hoc to resolve addresses to source locations via addr2line.

Differential profiling:
  Compare performance between two git refs (branches, commits, tags):

    scripts/profile_cbmc.py --diff develop my-feature-branch

  This builds both refs, runs the same benchmarks on each, and reports
  which functions got faster or slower.

Statistical significance:
  Use --runs N to run each benchmark multiple times. The summary will
  report mean ± stddev for timings:

    scripts/profile_cbmc.py --auto --runs 3

Examples:
  # Profile a single file
  scripts/profile_cbmc.py test.c -- --bounds-check --unwind 100

  # Run built-in benchmarks with source locations
  scripts/profile_cbmc.py --auto --debug-binary build-debug/bin/cbmc

  # Extended suite with CSmith-generated tests
  scripts/profile_cbmc.py --auto-large --auto-csmith

  # Compare two branches
  scripts/profile_cbmc.py --diff develop my-optimization-branch

  # Compare two existing result directories
  scripts/profile_cbmc.py --compare base-results pr-results \
    --compare-labels develop my-branch --output-dir diff-results

  # Multiple runs for statistical significance
  scripts/profile_cbmc.py --auto --runs 3

Future improvements:
  - Memory profiling: integrate heaptrack or valgrind --tool=massif to
    diagnose allocation-heavy code paths (malloc/free consistently show
    as ~35% of samples). Would require a separate recording pass since
    heaptrack instruments the allocator, not the CPU.
  - Incremental/cached profiling: cache results keyed by (git hash,
    benchmark name, cbmc args) to avoid re-running unchanged benchmarks.
    Would speed up repeated --diff runs on the same base ref.
  - LBR call graphs: on CPUs with Last Branch Record support, use
    --call-graph lbr for much smaller perf.data files with zero runtime
    overhead. Not universally available (requires hardware support).
  - Differential flamegraphs: generate red/blue diff flamegraphs between
    two refs using brendangregg/FlameGraph's difffolded.pl. Currently
    --diff only reports tabular comparisons.
  - CSmith seed curation: systematically select seeds that produce
    programs exercising specific CBMC features (heavy pointer use, deep
    nesting, many globals, etc.) rather than arbitrary fixed seeds.
  - CI differential mode: the CI workflow compares the PR branch against
    the base branch using --compare, posting regression warnings in the
    GitHub step summary. Could be extended to post PR comments.
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path

# Allow running as scripts/profile_cbmc.py from repo root
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.profiling.utils import (
    REPO_ROOT, check_prerequisites, die, ensure_cbmc, ensure_flamegraph, info, ok
)
from scripts.profiling.benchmarks import (
    generate_auto_benchmarks, generate_auto_large_benchmarks,
    generate_csmith_benchmarks,
)
from scripts.profiling.runner import (
    generate_aggregated_flamegraph, run_profile_set,
)
from scripts.profiling.analysis import (
    print_diff_summary, print_summary,
)


def build_ref(ref, work_dir, nproc):
    """Check out a git ref into work_dir and build CBMC. Returns cbmc path."""
    ref_dir = work_dir / ref.replace("/", "_")
    info(f"Building ref '{ref}' in {ref_dir}...")

    try:
        if not ref_dir.exists():
            subprocess.run(
                ["git", "worktree", "add", "--detach", str(ref_dir), ref],
                cwd=str(REPO_ROOT), check=True, capture_output=True)
            subprocess.run(
                ["git", "submodule", "update", "--init"],
                cwd=str(ref_dir), capture_output=True, check=True, timeout=120)

        build_dir = ref_dir / "build"
        subprocess.run(
            ["cmake", "-S", str(ref_dir), "-B", str(build_dir),
             "-DCMAKE_BUILD_TYPE=Release", "-DWITH_JBMC=OFF"],
            capture_output=True, check=True)

        for stamp in ["ansi-c", "cpp"]:
            stamp_file = build_dir / "src" / stamp / "library-check.stamp"
            stamp_file.parent.mkdir(parents=True, exist_ok=True)
            stamp_file.touch()

        subprocess.run(
            ["cmake", "--build", str(build_dir), "--target", "cbmc",
             "--target", "goto-cc", "-j", str(nproc)],
            capture_output=True, check=True, timeout=600)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
        die(f"Failed to build ref '{ref}': {e}")

    cbmc = ref_dir / "build" / "bin" / "cbmc"
    if not cbmc.is_file():
        die(f"CBMC binary not found after building ref '{ref}'")
    ok(f"Built {ref}: {cbmc}")
    return cbmc


def parse_args():
    argv = sys.argv[1:]
    cbmc_args = []
    if "--" in argv:
        idx = argv.index("--")
        cbmc_args = argv[idx + 1:]
        argv = argv[:idx]

    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("inputs", nargs="*", help="Input C files to profile")
    p.add_argument("--build-dir", default=str(REPO_ROOT / "build"))
    p.add_argument("--output-dir", default=str(REPO_ROOT / "profile-results"))
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--memory-limit", type=int, default=20480, help="MB")
    p.add_argument("--flamegraph-dir", default="")
    p.add_argument("--no-skip-solver", action="store_true")
    p.add_argument("--debug-binary", default="",
                   help="Path to CBMC binary with debug info (-g) for "
                        "source-level call site resolution")
    p.add_argument("--auto", action="store_true",
                   help="Generate and run built-in benchmarks (3 tests)")
    p.add_argument("--auto-large", action="store_true",
                   help="Generate and run extended benchmark suite (10 tests)")
    p.add_argument("--auto-csmith", action="store_true",
                   help="Generate benchmarks using CSmith with fixed seeds")
    p.add_argument("--diff", nargs=2, metavar=("REF_A", "REF_B"),
                   help="Differential profiling: compare two git refs")
    p.add_argument("--compare", nargs=2, metavar=("DIR_A", "DIR_B"),
                   help="Compare two existing result directories (each must "
                        "contain results.json)")
    p.add_argument("--compare-labels", nargs=2, metavar=("LABEL_A", "LABEL_B"),
                   default=None,
                   help="Labels for --compare (default: directory names)")
    p.add_argument("--runs", type=int, default=1,
                   help="Run each benchmark N times for statistical significance")
    args = p.parse_args(argv)
    args.cbmc_args = cbmc_args
    return args


def main():
    args = parse_args()
    output_dir = Path(args.output_dir)
    build_dir = Path(args.build_dir)
    skip_solver = not args.no_skip_solver

    # Differential mode
    if args.diff:
        ref_a, ref_b = args.diff
        check_prerequisites()
        fg_dir = ensure_flamegraph(args.flamegraph_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        nproc = os.cpu_count() or 4
        work_dir = output_dir / "worktrees"
        work_dir.mkdir(parents=True, exist_ok=True)

        cbmc_a = build_ref(ref_a, work_dir, nproc)
        cbmc_b = build_ref(ref_b, work_dir, nproc)

        benchmarks = generate_auto_benchmarks(output_dir)
        if args.auto_large:
            benchmarks = generate_auto_large_benchmarks(output_dir)
        if args.auto_csmith:
            benchmarks += generate_csmith_benchmarks(output_dir)
        for b in benchmarks:
            b["args"] = b.get("args", []) + args.cbmc_args

        dir_a = output_dir / f"ref_{ref_a.replace('/', '_')}"
        dir_b = output_dir / f"ref_{ref_b.replace('/', '_')}"

        info(f"Profiling {ref_a}...")
        results_a, _ = run_profile_set(
            cbmc_a, benchmarks, dir_a, fg_dir,
            args.timeout, args.memory_limit, skip_solver, args.runs)

        info(f"Profiling {ref_b}...")
        results_b, _ = run_profile_set(
            cbmc_b, benchmarks, dir_b, fg_dir,
            args.timeout, args.memory_limit, skip_solver, args.runs)

        if results_a and results_b:
            print()
            print_diff_summary(results_a, results_b, ref_a, ref_b, output_dir)

        # Clean up worktrees
        for ref in [ref_a, ref_b]:
            ref_dir = work_dir / ref.replace("/", "_")
            try:
                subprocess.run(
                    ["git", "worktree", "remove", "--force", str(ref_dir)],
                    cwd=str(REPO_ROOT), capture_output=True)
            except Exception:
                pass
        return

    # Compare mode: diff two existing result directories
    if args.compare:
        import json as _json
        dir_a, dir_b = Path(args.compare[0]), Path(args.compare[1])
        for d in (dir_a, dir_b):
            if not (d / "results.json").is_file():
                die(f"results.json not found in {d}")
        results_a = _json.loads((dir_a / "results.json").read_text())
        results_b = _json.loads((dir_b / "results.json").read_text())
        labels = args.compare_labels or [dir_a.name, dir_b.name]
        output_dir.mkdir(parents=True, exist_ok=True)
        print_diff_summary(results_a, results_b, labels[0], labels[1], output_dir)
        return

    # Normal mode
    has_auto = args.auto or args.auto_large or args.auto_csmith
    if not has_auto and not args.inputs:
        die("No input files specified. Use --auto, --auto-large, --auto-csmith, "
            "--diff, or --compare for built-in modes. Run with --help for usage.")

    check_prerequisites()
    cbmc = ensure_cbmc(build_dir)
    fg_dir = ensure_flamegraph(args.flamegraph_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    benchmarks = []
    if args.auto_large:
        benchmarks = generate_auto_large_benchmarks(output_dir)
    elif args.auto:
        benchmarks = generate_auto_benchmarks(output_dir)
    if args.auto_csmith:
        benchmarks += generate_csmith_benchmarks(output_dir)

    for b in benchmarks:
        b["args"] = b.get("args", []) + args.cbmc_args

    if args.inputs:
        for f in args.inputs:
            if not Path(f).is_file():
                die(f"Input file not found: {f}")
            benchmarks.append({
                "name": Path(f).stem,
                "file": str(Path(f).resolve()),
                "args": list(args.cbmc_args),
            })

    if not benchmarks:
        die("No benchmarks to run.")

    results, all_folded = run_profile_set(
        cbmc, benchmarks, output_dir, fg_dir,
        args.timeout, args.memory_limit, skip_solver, args.runs)

    if not results:
        die("No benchmarks produced results")

    if len(results) > 1 and all_folded:
        generate_aggregated_flamegraph(fg_dir, all_folded, output_dir)

    print()
    print_summary(results, output_dir, all_folded, args.debug_binary)


if __name__ == "__main__":
    main()
