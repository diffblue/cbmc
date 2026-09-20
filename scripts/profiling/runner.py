"""Benchmark runner and flamegraph generation."""

import re
import resource
import subprocess
import time
from pathlib import Path

from .utils import die, info, ok, warn

# DWARF stack dump size: 16384 bytes captures ~91% of full call stacks
# while producing 73% smaller perf.data files than the default 65528.
# Empirically validated: max stack depth 57 vs 54 at full size.
DWARF_STACK_SIZE = 16384

_perf_event_cache = None


def _detect_perf_event():
    """Detect whether hardware cycles counter is available, fall back to
    cpu-clock software event (for CI containers/VMs without PMU access).
    Both give equivalent function-level profiling results at 997 Hz."""
    global _perf_event_cache
    if _perf_event_cache is not None:
        return _perf_event_cache
    try:
        r = subprocess.run(
            ["perf", "record", "-e", "cycles", "-o", "/dev/null", "--",
             "true"],
            capture_output=True, timeout=5)
        if r.returncode == 0:
            _perf_event_cache = "cycles"
        else:
            _perf_event_cache = "cpu-clock"
    except (subprocess.TimeoutExpired, FileNotFoundError):
        _perf_event_cache = "cpu-clock"
    return _perf_event_cache


def compile_to_goto_binary(cbmc, source_file, output_dir):
    """Compile a C/C++ source file to a goto binary using goto-cc.

    Returns the path to the goto binary, or None if goto-cc is not available
    or compilation fails (in which case CBMC will parse the source directly).
    """
    goto_cc = Path(cbmc).parent / "goto-cc"
    if not goto_cc.is_file():
        return None

    gb_path = output_dir / (Path(source_file).stem + ".gb")
    try:
        subprocess.run(
            [str(goto_cc), "-o", str(gb_path), source_file],
            capture_output=True, check=True, timeout=60)
        return gb_path
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None


def run_benchmark(cbmc, bench, output_dir, timeout, memory_mb, skip_solver):
    """Run perf on a single benchmark. Returns parsed results dict."""
    name = bench["name"]
    bench_dir = output_dir / name
    bench_dir.mkdir(parents=True, exist_ok=True)

    # Pre-compile C/C++ sources to goto binaries for more stable measurements
    input_file = bench["file"]
    if Path(input_file).suffix in (".c", ".cpp", ".cc", ".h"):
        gb = compile_to_goto_binary(cbmc, input_file, bench_dir)
        if gb:
            input_file = str(gb)

    cmd = [str(cbmc), input_file] + bench.get("args", [])
    if skip_solver:
        if not any(a in cmd for a in ("--dimacs", "--smt2", "--show-vcc")):
            cmd += ["--dimacs", "--outfile", "/dev/null"]
    # --verbosity 8 == M_STATISTICS (see src/util/message.h); captures the
    # `Runtime ...` lines parsed below without enabling M_DEBUG=10, which
    # dumps every SSA step via SSA_stept::output and distorts the profile.
    cmd += ["--verbosity", "8"]

    perf_data = bench_dir / "perf.data"
    cbmc_output = bench_dir / "cbmc_output.txt"

    info(f"[{name}] Recording: {' '.join(cmd)}")

    # Try hardware cycles counter first (more precise); fall back to
    # cpu-clock software event if hardware PMU is unavailable (e.g., in
    # CI containers/VMs).
    perf_event = _detect_perf_event()

    perf_cmd = [
        "perf", "record", "-g",
        "--call-graph", f"dwarf,{DWARF_STACK_SIZE}",
        "-F", "997",
        "-e", perf_event,
        "-o", str(perf_data), "--"] + cmd

    start = time.monotonic()
    try:
        result = subprocess.run(
            perf_cmd, capture_output=True, text=True, timeout=timeout,
            preexec_fn=lambda: resource.setrlimit(
                resource.RLIMIT_AS, (memory_mb * 1024 * 1024, -1)))
        cbmc_stdout = result.stdout + result.stderr
        elapsed = time.monotonic() - start
    except subprocess.TimeoutExpired:
        elapsed = timeout
        cbmc_stdout = ""
        warn(f"[{name}] Timed out after {timeout}s — partial profile collected")

    cbmc_output.write_text(cbmc_stdout)

    if not perf_data.is_file():
        warn(f"[{name}] No perf data collected")
        return None

    ok(f"[{name}] perf data: {perf_data} "
       f"({perf_data.stat().st_size // 1024}K, {elapsed:.1f}s)")

    # Parse perf report
    report_txt = bench_dir / "perf-report.txt"
    report = subprocess.run(
        ["perf", "report", "-i", str(perf_data), "--stdio",
         "--no-children", "--percent-limit", "0.5", "-n"],
        capture_output=True, text=True)
    report_txt.write_text(report.stdout)

    functions = []
    for line in report.stdout.splitlines():
        m = re.match(r'\s+([\d.]+)%\s+(\d+)\s+\S+\s+(\S+)\s+\[.\]\s+(.*)', line)
        if m:
            functions.append({
                "pct": float(m.group(1)),
                "samples": int(m.group(2)),
                "module": m.group(3),
                "symbol": m.group(4),
            })

    # Parse CBMC timing from verbose output
    timings = {}
    for line in cbmc_stdout.splitlines():
        m = re.match(r'Runtime (\w[\w\s-]*\w): ([\d.e+-]+)s', line)
        if m:
            timings[m.group(1)] = float(m.group(2))
        m = re.match(r'size of program expression: (\d+) steps', line)
        if m:
            timings["program_steps"] = int(m.group(1))
        m = re.match(r'(?:simple )?slicing removed (\d+) assignments', line)
        if m:
            timings["sliced_assignments"] = int(m.group(1))

    # The regexes above are coupled to what CBMC currently emits via
    # log.statistics() / log.status(). If a future change reroutes a
    # timing line to log.progress() or log.debug(), or renames a prefix,
    # they would silently drop everything. Surface that loudly when we
    # have CBMC output (i.e., the run was not a timeout) but parsed
    # nothing, so a maintainer notices and updates the parser.
    if cbmc_stdout and not timings:
        warn(f"[{name}] No timing lines parsed from CBMC output; "
             f"the regexes in run_benchmark may have drifted from "
             f"CBMC's log.statistics() / log.status() output.")

    return {
        "name": name,
        "elapsed": elapsed,
        "timings": timings,
        "functions": functions[:30],
        "perf_data": str(perf_data),
        "bench_dir": str(bench_dir),
    }


def run_profile_set(cbmc, benchmarks, output_dir, fg_dir, timeout, memory_mb,
                    skip_solver, runs=1):
    """Run all benchmarks with a given CBMC binary, optionally multiple times.

    When runs > 1, returns averaged timings with stddev for statistical
    significance.
    """
    if runs == 1:
        results = []
        all_folded = []
        for bench in benchmarks:
            r = run_benchmark(cbmc, bench, output_dir,
                              timeout, memory_mb, skip_solver)
            if r:
                folded = generate_flamegraph(fg_dir, r)
                if folded:
                    all_folded.append(folded)
                results.append(r)
        return results, all_folded

    # Multi-run mode: run each benchmark `runs` times, average timings
    import statistics
    all_results = {}  # name -> [result, ...]
    for run_idx in range(runs):
        info(f"Run {run_idx + 1}/{runs}")
        run_dir = output_dir / f"run_{run_idx}"
        for bench in benchmarks:
            r = run_benchmark(cbmc, bench, run_dir,
                              timeout, memory_mb, skip_solver)
            if r:
                all_results.setdefault(bench["name"], []).append(r)

    # Average results, keep last run's perf data for flamegraphs
    results = []
    all_folded = []
    for bench in benchmarks:
        run_list = all_results.get(bench["name"], [])
        if not run_list:
            continue
        last = run_list[-1]
        # Compute mean and stddev for timings (union of all keys)
        all_timing_keys = set()
        for r in run_list:
            all_timing_keys.update(r["timings"].keys())
        avg_timings = {}
        for key in all_timing_keys:
            vals = [r["timings"].get(key, 0) for r in run_list]
            avg_timings[key] = statistics.mean(vals)
            if len(vals) > 1:
                avg_timings[f"{key}_stddev"] = statistics.stdev(vals)
        elapsed_vals = [r["elapsed"] for r in run_list]
        avg_elapsed = statistics.mean(elapsed_vals)

        result = {
            "name": last["name"],
            "elapsed": avg_elapsed,
            "timings": avg_timings,
            "functions": last["functions"],
            "perf_data": last["perf_data"],
            "bench_dir": last["bench_dir"],
            "runs": runs,
        }
        if len(elapsed_vals) > 1:
            result["elapsed_stddev"] = statistics.stdev(elapsed_vals)

        folded = generate_flamegraph(fg_dir, result)
        if folded:
            all_folded.append(folded)
        results.append(result)

    return results, all_folded


def generate_flamegraph(fg_dir, result, title_suffix=""):
    """Generate flamegraph SVG from perf data. Returns folded stacks or None."""
    bench_dir = Path(result["bench_dir"])
    perf_data = result["perf_data"]
    svg = bench_dir / "flamegraph.svg"

    try:
        script = subprocess.run(
            ["perf", "script", "-i", perf_data],
            capture_output=True, text=True, timeout=120)
        if script.returncode != 0:
            warn(f"[{result['name']}] perf script failed (exit {script.returncode})")
            return None

        collapse = subprocess.run(
            [str(fg_dir / "stackcollapse-perf.pl")],
            input=script.stdout, capture_output=True, text=True, timeout=60)

        if not collapse.stdout.strip():
            warn(f"[{result['name']}] No stack data to generate flamegraph")
            return None

        title = f"CBMC Profile: {result['name']}{title_suffix}"
        fg_result = subprocess.run(
            [str(fg_dir / "flamegraph.pl"), "--title", title],
            input=collapse.stdout, capture_output=True, text=True, timeout=60)
        if fg_result.returncode != 0:
            warn(f"[{result['name']}] flamegraph.pl failed")
            return None

        svg.write_text(fg_result.stdout)
        ok(f"[{result['name']}] Flamegraph: {svg}")
        return collapse.stdout
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError, OSError) as e:
        warn(f"[{result['name']}] Flamegraph generation failed: {e}")
        return None


def generate_aggregated_flamegraph(fg_dir, all_folded, output_dir):
    """Generate a combined flamegraph from all benchmarks."""
    combined = "\n".join(all_folded)
    svg = output_dir / "aggregated.svg"
    try:
        fg_result = subprocess.run(
            [str(fg_dir / "flamegraph.pl"),
             "--title", "CBMC Aggregated Profile (all benchmarks)"],
            input=combined, capture_output=True, text=True, timeout=60)
        svg.write_text(fg_result.stdout)
        ok(f"Aggregated flamegraph: {svg}")
    except (subprocess.TimeoutExpired, OSError) as e:
        warn(f"Aggregated flamegraph failed: {e}")
