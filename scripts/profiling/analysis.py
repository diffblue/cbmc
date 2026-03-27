"""Profiling analysis: call chains, source resolution, interpretation."""

import json
import re
import subprocess
from pathlib import Path

from .utils import REPO_ROOT, info, ok, warn


def _shorten_symbol(sym):
    """Strip template noise for readability."""
    result = re.sub(r'std::_Hashtable<[^>]+>', 'std::_Hashtable<...>', sym)
    result = re.sub(r'std::_Function_handler<[^>]+>', 'std::_Function_handler<...>', result)
    result = re.sub(r'sharing_treet<[^>]+>', 'sharing_treet<...>', result)
    result = re.sub(r'tree_nodet<[^>]+>', 'tree_nodet<...>', result)
    result = re.sub(r'renamedt<[^>]+>', 'renamedt<...>', result)
    result = re.sub(r'std::map<[^>]+>', 'std::map<...>', result)
    result = re.sub(r'std::vector<[^>]+>', 'std::vector<...>', result)
    result = re.sub(r'std::function<[^>]+>', 'std::function<...>', result)
    result = re.sub(r'std::__cxx11::basic_string<[^>]+>', 'std::string', result)
    result = re.sub(r'std::basic_ostream<[^>]+>', 'std::ostream', result)
    result = re.sub(r'\s*\(inlined\)', '', result)
    result = re.sub(r'\s*\[clone [^\]]+\]', '', result)
    return result


_INFRA_FUNCTIONS = {
    "_start", "__libc_start_main_impl", "__libc_start_call_main",
    "main", "parse_options_baset::main()", "cbmc_parse_optionst::doit()",
}


def _is_interesting_caller(fn):
    if fn in _INFRA_FUNCTIONS:
        return False
    if fn.startswith("std::") or fn.startswith("__"):
        return False
    if fn in ("operator new(unsigned long)", "operator delete(void*)"):
        return False
    return True


def analyze_call_chains(all_folded):
    """Parse folded stacks to find callers of hotspot functions."""
    hotspot_data = {}
    for folded_text in all_folded:
        for line in folded_text.strip().splitlines():
            parts = line.rsplit(" ", 1)
            if len(parts) != 2:
                continue
            stack_str, count_str = parts
            try:
                count = int(count_str)
            except ValueError:
                continue
            frames = stack_str.split(";")
            for i, frame in enumerate(frames):
                if frame not in hotspot_data:
                    hotspot_data[frame] = {"total": 0, "callers": {}, "call_paths": {}}
                hotspot_data[frame]["total"] += count
                if i > 0:
                    direct_caller = frames[i - 1]
                    hotspot_data[frame]["callers"][direct_caller] = \
                        hotspot_data[frame]["callers"].get(direct_caller, 0) + count
                    for j in range(i - 1, -1, -1):
                        if _is_interesting_caller(frames[j]):
                            key = (frames[j], direct_caller)
                            hotspot_data[frame]["call_paths"][key] = \
                                hotspot_data[frame]["call_paths"].get(key, 0) + count
                            break
    return hotspot_data


def resolve_call_sites(perf_data_files, cbmc_bin):
    """Resolve caller offsets to source file:line via addr2line."""
    has_debug = False
    try:
        result = subprocess.run(
            ["readelf", "-S", str(cbmc_bin)],
            capture_output=True, text=True, timeout=10)
        has_debug = ".debug_info" in result.stdout
    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass

    if not has_debug:
        return None

    nm_result = subprocess.run(
        ["nm", "--demangle", str(cbmc_bin)], capture_output=True, text=True)
    sym_addrs = {}
    for line in nm_result.stdout.splitlines():
        parts = line.split(None, 2)
        if len(parts) == 3 and parts[1] in ("T", "t", "W", "w"):
            sym_addrs[parts[2]] = int(parts[0], 16)

    call_sites = {}
    frame_re = re.compile(
        r'\s+([0-9a-f]+)\s+(.+?)\+0x([0-9a-f]+)\s+\(.*cbmc\)')

    for perf_data in perf_data_files:
        try:
            script = subprocess.run(
                ["perf", "script", "-i", str(perf_data)],
                capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            continue

        prev_frame = None
        for line in script.stdout.splitlines():
            m = frame_re.match(line)
            if m:
                sym = m.group(2)
                offset = int(m.group(3), 16)
                if prev_frame:
                    callee_sym = prev_frame[0]
                    key = (sym, offset)
                    call_sites.setdefault(callee_sym, {})
                    call_sites[callee_sym][key] = \
                        call_sites[callee_sym].get(key, 0) + 1
                prev_frame = (sym, offset)
            elif line.strip() == "" or not line.startswith("\t"):
                prev_frame = None

    addrs_to_resolve = set()
    for callee, callers in call_sites.items():
        for (caller_sym, caller_offset), _ in callers.items():
            base = sym_addrs.get(caller_sym)
            if base is None:
                prefix = caller_sym.split("(")[0]
                for nm_sym, addr in sym_addrs.items():
                    if nm_sym.startswith(prefix + "(") or nm_sym == prefix:
                        base = addr
                        break
            if base is not None:
                addrs_to_resolve.add((caller_sym, caller_offset, base + caller_offset))

    if not addrs_to_resolve:
        return call_sites

    addr_list = sorted(addrs_to_resolve, key=lambda x: x[2])
    addr_strs = [f"0x{a[2]:x}" for a in addr_list]

    try:
        a2l = subprocess.run(
            ["addr2line", "-e", str(cbmc_bin), "-f", "-i"] + addr_strs,
            capture_output=True, text=True, timeout=30)
    except subprocess.TimeoutExpired:
        return call_sites

    a2l_lines = a2l.stdout.strip().splitlines()
    source_map = {}
    for i, (sym, offset, _) in enumerate(addr_list):
        idx = i * 2
        if idx + 1 < len(a2l_lines):
            loc = a2l_lines[idx + 1]
            if loc and "?" not in loc:
                loc = loc.replace(str(REPO_ROOT) + "/", "")
                source_map[(sym, offset)] = loc

    result = {}
    for callee, callers in call_sites.items():
        entries = []
        for (caller_sym, caller_offset), count in callers.items():
            loc = source_map.get((caller_sym, caller_offset), "")
            entries.append((caller_sym, loc, count))
        result[callee] = entries

    return result


def interpret_results(results, all_folded, source_sites=None):
    """Produce actionable hotspot analysis with call chains and source locations."""
    lines = []

    def out(s=""):
        lines.append(s)

    agg = {}
    per_bench = {}
    total_samples = 0
    for r in results:
        for f in r["functions"]:
            key = (f["module"], f["symbol"])
            agg[key] = agg.get(key, 0) + f["samples"]
            total_samples += f["samples"]
            per_bench.setdefault(key, {})[r["name"]] = \
                per_bench.get(key, {}).get(r["name"], 0) + f["samples"]

    if not total_samples:
        return ["Insufficient samples collected — try longer-running benchmarks."]

    def pct(n):
        return 100.0 * n / total_samples

    chain_data = analyze_call_chains(all_folded) if all_folded else {}

    cbmc_fns = sorted(
        ((k, v) for k, v in agg.items() if k[0] == "cbmc"),
        key=lambda x: -x[1])

    out("For each hotspot: callers are extracted from perf call stacks.")
    out("Open the per-benchmark flamegraph SVGs for interactive exploration.")
    out("")

    for (mod, sym), samples in cbmc_fns[:8]:
        if pct(samples) < 1.0:
            break

        short_sym = _shorten_symbol(sym)
        out(f"{'─' * 72}")
        out(f"  {short_sym}")
        out(f"  {pct(samples):.1f}% of total samples ({samples} samples)")

        bench_contribs = per_bench.get((mod, sym), {})
        if len(bench_contribs) > 1:
            sorted_benches = sorted(bench_contribs.items(), key=lambda x: -x[1])
            bench_parts = [f"{name}={cnt}" for name, cnt in sorted_benches[:4]]
            out(f"  Benchmarks: {', '.join(bench_parts)}")

        cdata = chain_data.get(sym)
        if not cdata:
            for k, v in chain_data.items():
                if sym.split("(")[0] in k:
                    cdata = v
                    break

        if cdata and cdata["callers"]:
            sorted_callers = sorted(cdata["callers"].items(), key=lambda x: -x[1])
            caller_total = sum(c for _, c in sorted_callers)
            out(f"  Direct callers (from perf call stacks):")
            for caller, cnt in sorted_callers[:5]:
                caller_pct = 100.0 * cnt / caller_total
                short_caller = _shorten_symbol(caller)
                if len(short_caller) > 65:
                    short_caller = short_caller[:62] + "..."
                out(f"    {caller_pct:5.1f}%  {short_caller}")

            if cdata["call_paths"]:
                sorted_paths = sorted(cdata["call_paths"].items(), key=lambda x: -x[1])
                path_total = sum(c for _, c in sorted_paths)
                out(f"  Top call paths (nearest CBMC caller → hotspot):")
                seen_callers = set()
                shown = 0
                for (interesting, direct), cnt in sorted_paths:
                    if interesting in seen_callers:
                        continue
                    seen_callers.add(interesting)
                    path_pct = 100.0 * cnt / path_total
                    short_int = _shorten_symbol(interesting)
                    if len(short_int) > 55:
                        short_int = short_int[:52] + "..."
                    short_dir = _shorten_symbol(direct)
                    if len(short_dir) > 55:
                        short_dir = short_dir[:52] + "..."
                    if interesting == direct:
                        out(f"    {path_pct:5.1f}%  {short_int}")
                    else:
                        out(f"    {path_pct:5.1f}%  {short_int}")
                        out(f"           → {short_dir}")
                    shown += 1
                    if shown >= 4:
                        break

        if source_sites and sym in source_sites:
            loc_counts = {}
            for caller_sym, loc, count in source_sites[sym]:
                if loc:
                    short_c = _shorten_symbol(caller_sym)
                    if len(short_c) > 45:
                        short_c = short_c[:42] + "..."
                    key = (loc, short_c)
                    loc_counts[key] = loc_counts.get(key, 0) + count
            if loc_counts:
                sorted_locs = sorted(loc_counts.items(), key=lambda x: -x[1])
                loc_total = sum(c for _, c in sorted_locs)
                out(f"  Call sites with source locations:")
                for (loc, caller), cnt in sorted_locs[:6]:
                    loc_pct = 100.0 * cnt / loc_total
                    out(f"    {loc_pct:5.1f}%  {loc}")
                    out(f"           in {caller}")

        out("")

    out(f"{'─' * 72}")
    out("DRILL-DOWN COMMANDS")
    out("")
    out("To investigate a specific function's callers in detail:")
    out("  perf report -i profile-results/<benchmark>/perf.data \\")
    out("    --stdio --no-children --symbol-filter='<function>' \\")
    out("    -g caller,folded,0.5")
    out("")
    out("To get an interactive TUI for any benchmark:")
    out("  perf report -i profile-results/<benchmark>/perf.data -g caller")
    out("")

    slow_symex = [r for r in results
                  if r["timings"].get("Symex", 0) > 0.5 * r["elapsed"]
                  and r["elapsed"] > 1.0]
    slow_convert = [r for r in results
                    if r["timings"].get("Convert SSA", 0) > 0.3 * r["elapsed"]
                    and r["elapsed"] > 1.0]
    if slow_symex:
        names = ", ".join(r["name"] for r in slow_symex)
        out(f"SYMEX-DOMINATED: {names}")
        out(f"  Symex takes >50% of wall time. Start with the flamegraph for")
        out(f"  these benchmarks and look at goto_symext:: call subtrees.")
        out(f"  Source: src/goto-symex/")
        out("")
    if slow_convert:
        names = ", ".join(r["name"] for r in slow_convert)
        out(f"SSA-CONVERSION-DOMINATED: {names}")
        out(f"  Propositional encoding takes >30% of wall time.")
        out(f"  Source: src/solvers/flattening/")
        out("")

    return lines


def print_summary(results, output_dir, all_folded, debug_binary=None):
    """Print and save a summary of all benchmark results."""
    lines = []

    def out(s=""):
        lines.append(s)
        print(s)

    out("=" * 72)
    out("CBMC PROFILING SUMMARY")
    out("=" * 72)

    has_stddev = any(r.get("runs", 1) > 1 for r in results)
    out("\n--- CBMC Internal Timings ---\n")
    hdr = f"{'Benchmark':<20} {'Symex':>10} {'Convert':>10} {'Solver':>10} {'Total':>10} {'Steps':>10}"
    if has_stddev:
        hdr += f" {'±Total':>8}"
    out(hdr)
    out("-" * (72 + (9 if has_stddev else 0)))
    for r in results:
        t = r["timings"]
        line = (f"{r['name']:<20} "
                f"{t.get('Symex', 0):>9.3f}s "
                f"{t.get('Convert SSA', 0):>9.3f}s "
                f"{t.get('Solver', 0):>9.3f}s "
                f"{r['elapsed']:>9.1f}s "
                f"{t.get('program_steps', 0):>10}")
        if has_stddev and "elapsed_stddev" in r:
            line += f" ±{r['elapsed_stddev']:.2f}s"
        out(line)

    out("\n--- Aggregated Top Functions (by samples) ---\n")
    agg = {}
    total_samples = 0
    for r in results:
        for f in r["functions"]:
            key = (f["module"], f["symbol"])
            agg[key] = agg.get(key, 0) + f["samples"]
            total_samples += f["samples"]

    sorted_fns = sorted(agg.items(), key=lambda x: -x[1])[:25]
    out(f"{'%':>6} {'Samples':>8}  {'Module':<30} Symbol")
    out("-" * 72)
    for (mod, sym), samples in sorted_fns:
        pct = 100.0 * samples / total_samples if total_samples else 0
        mod_short = mod if len(mod) <= 30 else "..." + mod[-27:]
        out(f"{pct:>5.1f}% {samples:>8}  {mod_short:<30} {sym}")

    cbmc_samples = sum(s for (m, _), s in agg.items() if m == "cbmc")
    lib_samples = total_samples - cbmc_samples
    out(f"\n--- Sample Distribution ---")
    out(f"  CBMC code:    {cbmc_samples:>8} ({100*cbmc_samples/max(total_samples,1):.1f}%)")
    out(f"  Libraries:    {lib_samples:>8} ({100*lib_samples/max(total_samples,1):.1f}%)")
    out(f"  Total:        {total_samples:>8}")

    out(f"\n--- Output Files ---")
    for r in results:
        out(f"  {r['name']}/flamegraph.svg")
        out(f"  {r['name']}/perf-report.txt")
    out(f"  aggregated.svg")
    out(f"  summary.txt")
    out(f"\nResults directory: {output_dir}")
    out("=" * 72)

    # Resolve source-level call sites
    cbmc_bin = None
    if debug_binary and Path(debug_binary).is_file():
        cbmc_bin = Path(debug_binary)
    else:
        for candidate in [REPO_ROOT / "build-debug" / "bin" / "cbmc",
                          REPO_ROOT / "build" / "bin" / "cbmc"]:
            if candidate.is_file():
                cbmc_bin = candidate
                break

    source_sites = None
    if cbmc_bin:
        source_sites = resolve_call_sites(
            [Path(r["perf_data"]) for r in results], cbmc_bin)
    if source_sites is None:
        info("No debug info found — source locations unavailable.")
        info("For source-level detail, build with -DCMAKE_BUILD_TYPE=RelWithDebInfo")
        info("and pass --debug-binary build-debug/bin/cbmc")
        source_sites = {}

    suggestions = interpret_results(results, all_folded, source_sites)
    out("")
    out("=" * 72)
    out("ACTIONABLE HOTSPOT ANALYSIS")
    out("=" * 72)
    out("")
    for s in suggestions:
        out(s)

    (output_dir / "summary.txt").write_text("\n".join(lines) + "\n")
    (output_dir / "results.json").write_text(
        json.dumps(results, indent=2, default=str) + "\n")


def print_diff_summary(results_a, results_b, ref_a, ref_b, output_dir):
    """Compare profiling results between two refs."""
    lines = []

    def out(s=""):
        lines.append(s)
        print(s)

    out("=" * 72)
    out(f"DIFFERENTIAL PROFILE: {ref_a} vs {ref_b}")
    out("=" * 72)

    by_name_a = {r["name"]: r for r in results_a}
    by_name_b = {r["name"]: r for r in results_b}
    common = sorted(set(by_name_a) & set(by_name_b))

    if not common:
        out("No common benchmarks to compare.")
        return

    out(f"\n--- Timing Comparison (pre-solver) ---\n")
    out(f"{'Benchmark':<20} {ref_a[:12]:>12} {ref_b[:12]:>12} {'Change':>10}")
    out("-" * 56)
    for name in common:
        ra, rb = by_name_a[name], by_name_b[name]
        ta = ra["timings"].get("Symex", 0) + ra["timings"].get("Convert SSA", 0)
        tb = rb["timings"].get("Symex", 0) + rb["timings"].get("Convert SSA", 0)
        if ta > 0.01:
            change = (tb - ta) / ta * 100
            marker = "⚡" if change < -5 else ("⚠️" if change > 5 else "")
            out(f"{name:<20} {ta:>11.3f}s {tb:>11.3f}s {change:>+9.1f}% {marker}")
        else:
            out(f"{name:<20} {ta:>11.3f}s {tb:>11.3f}s {'(too fast)':>10}")

    out(f"\n--- Function Sample Comparison (top changes) ---\n")
    agg_a, agg_b = {}, {}
    total_a = total_b = 0
    for r in results_a:
        for f in r["functions"]:
            if f["module"] == "cbmc":
                agg_a[f["symbol"]] = agg_a.get(f["symbol"], 0) + f["samples"]
                total_a += f["samples"]
    for r in results_b:
        for f in r["functions"]:
            if f["module"] == "cbmc":
                agg_b[f["symbol"]] = agg_b.get(f["symbol"], 0) + f["samples"]
                total_b += f["samples"]

    all_syms = set(agg_a) | set(agg_b)
    diffs = []
    for sym in all_syms:
        pct_a = 100.0 * agg_a.get(sym, 0) / max(total_a, 1)
        pct_b = 100.0 * agg_b.get(sym, 0) / max(total_b, 1)
        delta = pct_b - pct_a
        if abs(delta) > 0.5:
            diffs.append((sym, pct_a, pct_b, delta))

    diffs.sort(key=lambda x: -abs(x[3]))
    out(f"{'Symbol':<55} {ref_a[:6]:>6} {ref_b[:6]:>6} {'Δ':>6}")
    out("-" * 72)
    for sym, pa, pb, delta in diffs[:15]:
        short = _shorten_symbol(sym)
        if len(short) > 54:
            short = short[:51] + "..."
        marker = "⚡" if delta < -1 else ("⚠️" if delta > 1 else "")
        out(f"{short:<55} {pa:>5.1f}% {pb:>5.1f}% {delta:>+5.1f}% {marker}")

    out(f"\nResults: {output_dir}")
    out("=" * 72)

    (output_dir / "diff_summary.txt").write_text("\n".join(lines) + "\n")
