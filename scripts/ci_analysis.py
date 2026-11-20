#!/usr/bin/env python3

"""
Analyse GitHub Actions CI logs for the diffblue/cbmc repository.

Downloads logs for recent completed runs of the "Build and Test CBMC" workflow
(and optionally other workflows), then reports:

  1. Per-job wall-clock durations (sorted slowest-first).
  2. Per-step durations inside each job (build, test, setup, etc.).
  3. Per-suite durations for both ctest-based (CMake) and make-based jobs.
  4. Per-test durations *within* each slow suite (drill-down).
  5. A cross-run summary aggregating all of the above across N runs.

The script supports three distinct log formats produced by the CI:

  - **ctest verbose output** (CMake jobs): parses ``Test #N: suite ... Passed Xs``
    lines for suite-level timing, and ``N: Running test [OK] in Xs`` lines from
    test.pl for individual test timing within each suite.
  - **make parallel output** (Linux make jobs): parses ``N: Running suite...``
    and ``N: All tests were successful`` with runner-ID prefixes.
  - **make serial output** (Windows VS 2022 make job): same as above but without
    runner-ID prefixes (``Running suite...`` / ``All tests were successful``).
  - **validate-trace-xml-schema**: uses timestamp differences between consecutive
    ``*** Checking [N/M]`` lines to compute per-test durations.

Usage examples::

    # Analyse 5 recent runs of the main workflow (default)
    python3 scripts/ci_analysis.py

    # Analyse 10 runs, show top 30 items in each summary section
    python3 scripts/ci_analysis.py --runs 10 --top 30

    # Analyse a different workflow (by name or filename)
    python3 scripts/ci_analysis.py --workflow coverage.yaml

    # Cache logs in a specific directory (avoids re-downloading)
    python3 scripts/ci_analysis.py --log-dir /tmp/my-ci-logs

    # Produce markdown output suitable for GitHub Actions job summaries
    python3 scripts/ci_analysis.py --markdown

Requirements:
    - The ``gh`` CLI (https://cli.github.com/) must be installed and
      authenticated with access to the target repository.
    - Python 3.8+
    - No third-party Python packages required.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import zipfile
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from statistics import median as _median


# ── helpers ──────────────────────────────────────────────────────────────────

# When --quiet is active, info() output is suppressed.
_quiet = False


def info(*args, **kwargs):
    """Print progress/diagnostic information (suppressed by --quiet)."""
    if not _quiet:
        print(*args, **kwargs)

def run_gh(*args: str, repo: str = "") -> str:
    """Run a ``gh`` CLI command and return its stdout.

    If *repo* is provided, any ``{owner}/{repo}`` placeholder in the
    arguments is replaced with the actual repository identifier.
    For non-API commands (``run``, ``workflow``, etc.) the ``-R`` flag
    is added automatically so that the correct repository is targeted
    even when running from a fork.
    """
    if repo:
        args = tuple(a.replace("{owner}/{repo}", repo) for a in args)
        if args and args[0] != "api":
            args = args + ("-R", repo)
    result = subprocess.run(
        ["gh"] + list(args),
        capture_output=True, text=True, check=True,
    )
    return result.stdout


def parse_ts(ts_str: str) -> datetime:
    """Parse an ISO-8601 timestamp (with or without trailing Z)."""
    ts_str = ts_str.rstrip("Z").rstrip("\r\n")
    # Handle fractional seconds of varying length
    if "." in ts_str:
        base, frac = ts_str.split(".")
        frac = frac[:6]  # truncate to microseconds
        ts_str = f"{base}.{frac}"
    return datetime.fromisoformat(ts_str).replace(tzinfo=timezone.utc)


def fmt_duration(seconds: float) -> str:
    """Format seconds as ``Xh Ym Zs`` or ``Ym Zs`` or ``Zs``."""
    if seconds < 0:
        return "???"
    m, s = divmod(int(seconds), 60)
    h, m = divmod(m, 60)
    if h:
        return f"{h}h {m:02d}m {s:02d}s"
    if m:
        return f"{m}m {s:02d}s"
    return f"{s}s"


def median(values: list[float]) -> float:
    """Return the median of *values* (0.0 for an empty list).

    The median is preferred over the mean for the cross-run summaries: macOS
    runners in particular vary by 30-40% run-to-run, and a single slow run
    would skew a mean. The median is robust to such outliers, so a change in
    the median across many runs is a much stronger signal of a real
    regression than a change in a single run or in the mean.

    This wraps ``statistics.median`` purely to add the 0.0-for-empty
    behaviour, which several callers (e.g. ``_critical_paths``, ``_stats``)
    rely on.
    """
    return _median(values) if values else 0.0


# ── log timestamp extraction ────────────────────────────────────────────────

# GitHub Actions log lines start with an ISO timestamp, e.g.
#   2026-03-10T01:32:15.1159060Z ...
_TS_RE = re.compile(r"^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+)Z\s")


def extract_first_last_ts(lines: list[str]) -> tuple[datetime | None,
                                                      datetime | None]:
    """Return (first_timestamp, last_timestamp) from log lines."""
    first = last = None
    for line in lines:
        m = _TS_RE.match(line)
        if m:
            ts = parse_ts(m.group(1))
            if first is None:
                first = ts
            last = ts
    return first, last


# ── step-level parsing ──────────────────────────────────────────────────────

# Steps are delimited by  ##[group]Run ...  lines.
_STEP_RE = re.compile(
    r"^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+)Z\s+##\[group\]Run\s+(.*)"
)


def parse_steps(lines: list[str]) -> list[dict]:
    """Return a list of {name, start, end, duration_s} dicts for each step."""
    markers: list[tuple[datetime, str, int]] = []
    for idx, line in enumerate(lines):
        m = _STEP_RE.match(line)
        if m:
            markers.append((parse_ts(m.group(1)), m.group(2).strip(), idx))

    steps = []
    for i, (start, name, start_idx) in enumerate(markers):
        # end = start of next step, or last timestamp in file
        if i + 1 < len(markers):
            end = markers[i + 1][0]
        else:
            _, end = extract_first_last_ts(lines[start_idx:])
            if end is None:
                end = start
        dur = (end - start).total_seconds()
        steps.append({"name": name, "start": start, "end": end,
                       "duration_s": dur})
    return steps


# ── ctest output parsing ────────────────────────────────────────────────────

# ctest -V lines look like:
#   66/88 Test #239: book-examples-CORE ...  Passed  214.15 sec
_CTEST_RE = re.compile(
    r"Test\s+#\d+:\s+(\S+)\s+\.+\s+(Passed|Failed)\s+([\d.]+)\s+sec"
)

# Total Test time (real) = 8355.48 sec
_CTEST_TOTAL_RE = re.compile(r"Total Test time \(real\)\s*=\s*([\d.]+)\s*sec")


def parse_ctest(lines: list[str]) -> list[dict]:
    """Parse ctest verbose output, returning per-test durations."""
    tests = []
    for line in lines:
        m = _CTEST_RE.search(line)
        if m:
            tests.append({
                "name": m.group(1),
                "status": m.group(2),
                "duration_s": float(m.group(3)),
            })
    tests.sort(key=lambda t: t["duration_s"], reverse=True)
    return tests


# ── individual test parsing within ctest suites ─────────────────────────────

# Within ctest verbose output, each suite's individual tests are prefixed
# with the ctest test number.  test.pl output looks like:
#   263:   Running StringSubstring/test.desc  [OK] in 1950 seconds
# The ANSI colour codes around OK/FAILED are stripped by the regex.
_INDIVIDUAL_TEST_RE = re.compile(
    r"^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+)Z\s+"
    r"(\d+):\s+Running\s+(\S+)\s+\[.*?\]\s+in\s+(\d+)\s+seconds"
)

# validate-trace-xml-schema uses a different format:
#   213: *** Checking [1/1107] .../regression/cbmc/Foo/test.desc... [SUCCESS]
_VALIDATE_XML_RE = re.compile(
    r"^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+)Z\s+"
    r"(\d+):\s+\*\*\*\s+Checking\s+\[\d+/\d+\]\s+.*?regression/(\S+)\.\.\."
)

# ctest "Start" line to map test numbers to suite names:
#   Start 263: jbmc-strings-symex-driven-lazy-loading-CORE
_CTEST_START_RE = re.compile(
    r"Start\s+(\d+):\s+(\S+)"
)

# make-based suite header (with optional runner-ID prefix):
#   Running cbmc...           (serial)
#   3:	Running cbmc...   (parallel, with runner id)
_MAKE_SUITE_HEADER_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+Z\s+"
    r"(?:(\d+):\s+)?Running\s+(\S+)\.\.\."
)

# make-based individual test (with optional runner-ID prefix, indented):
#   Running foo/test.desc  [OK] in 5 seconds          (serial)
#   3:	  Running foo/test.desc  [OK] in 5 seconds    (parallel)
_MAKE_INDIVIDUAL_TEST_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+Z\s+"
    r"(?:(\d+):\s+)?\s+Running\s+(\S+)\s+\[.*?\]\s+in\s+(\d+)\s+seconds"
)


def parse_individual_tests(lines: list[str]) -> dict[str, list[dict]]:
    """Parse individual test durations within each ctest suite.

    Returns a dict mapping suite name to a list of
    ``{name, duration_s}`` dicts (sorted slowest-first).
    Supports three formats:
    - ctest/test.pl with numeric prefix (``263: Running foo [OK] in 5 seconds``)
    - validate-trace-xml-schema (timestamp-based)
    - make-based test.pl without prefix (``Running foo [OK] in 5 seconds``)
    """
    # Build test-number -> suite-name mapping
    num_to_suite: dict[str, str] = {}
    for line in lines:
        m = _CTEST_START_RE.search(line)
        if m:
            num_to_suite[m.group(1)] = m.group(2)

    # Collect individual test results keyed by suite
    suite_tests: dict[str, list[dict]] = defaultdict(list)

    # 1) test.pl style with ctest number prefix: "263: Running foo [OK] in N seconds"
    #    Only use this branch when we have a ctest num->suite mapping,
    #    otherwise the regex also matches make-parallel runner-ID lines.
    if num_to_suite:
        for line in lines:
            m = _INDIVIDUAL_TEST_RE.match(line)
            if m:
                test_num = m.group(2)
                suite = num_to_suite.get(test_num, f"suite-{test_num}")
                suite_tests[suite].append({
                    "name": m.group(3),
                    "duration_s": int(m.group(4)),
                })

    # 2) validate-trace-xml-schema style: compute from timestamps.
    #    Only applies to ctest-based jobs (where num_to_suite is populated).
    if num_to_suite:
        validate_entries: dict[str, list[tuple[datetime, str]]] = \
            defaultdict(list)
        for line in lines:
            m = _VALIDATE_XML_RE.match(line)
            if m:
                ts = parse_ts(m.group(1))
                test_num = m.group(2)
                suite = num_to_suite.get(test_num, f"suite-{test_num}")
                test_name = m.group(3)
                validate_entries[suite].append((ts, test_name))

        for suite, entries in validate_entries.items():
            if suite in suite_tests:
                continue  # already parsed via test.pl
            for i in range(len(entries) - 1):
                dur = (entries[i + 1][0] - entries[i][0]).total_seconds()
                suite_tests[suite].append({
                    "name": entries[i][1],
                    "duration_s": dur,
                })

    # 3) make-based test.pl (serial or parallel with runner-ID prefix).
    #    Suite boundaries are "Running <suite>..." lines; individual tests
    #    are "  Running <test>  [OK] in N seconds" (indented).
    #    For parallel output, track current suite per runner ID.
    if not suite_tests:
        # runner_id -> current suite name (None = serial / single runner)
        suite_by_runner: dict[str | None, str | None] = {}
        for line in lines:
            m = _MAKE_SUITE_HEADER_RE.match(line)
            if m:
                runner_id = m.group(1)  # None for serial
                suite_by_runner[runner_id] = m.group(2)
                continue
            m = _MAKE_INDIVIDUAL_TEST_RE.match(line)
            if m:
                runner_id = m.group(1)  # None for serial
                current_suite = suite_by_runner.get(runner_id)
                if current_suite is None:
                    continue
                suite_tests[current_suite].append({
                    "name": m.group(2),
                    "duration_s": int(m.group(3)),
                })

    # Sort each suite's tests by duration
    for suite in suite_tests:
        suite_tests[suite].sort(
            key=lambda t: t["duration_s"], reverse=True)

    return dict(suite_tests)



# make-based test output has lines like:
#   N:\tRunning <suite>...          (parallel, with runner id)
#   Running <suite>...              (serial, no runner id)
#   N:\tAll tests were successful
#   All tests were successful       (serial)
# We compute suite duration from timestamps of "Running" to "All tests".

_MAKE_SUITE_START_RE = re.compile(
    r"^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+)Z\s+"
    r"(?:(\d+):\s+)?Running\s+(\S+)\.\.\."
)
_MAKE_SUITE_END_RE = re.compile(
    r"^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+)Z\s+"
    r"(?:(\d+):\s+)?.*(?:All tests were successful|tests? failed)"
)


def parse_make_suites(lines: list[str]) -> list[dict]:
    """Parse make-based test output for per-suite durations."""
    # Track suite starts by runner id (or "_serial" for non-parallel)
    active: dict[str, tuple[datetime, str]] = {}
    suites = []

    for line in lines:
        m = _MAKE_SUITE_START_RE.match(line)
        if m:
            ts = parse_ts(m.group(1))
            rid = m.group(2) or "_serial"
            suite_name = m.group(3)
            active[rid] = (ts, suite_name)
            continue

        m = _MAKE_SUITE_END_RE.match(line)
        if m:
            ts = parse_ts(m.group(1))
            rid = m.group(2) or "_serial"
            if rid in active:
                start_ts, suite_name = active.pop(rid)
                dur = (ts - start_ts).total_seconds()
                suites.append({"name": suite_name, "duration_s": dur})

    suites.sort(key=lambda s: s["duration_s"], reverse=True)
    return suites


# ── job-level analysis from API ─────────────────────────────────────────────

def get_job_durations(run_id: int, repo: str = "") -> list[dict]:
    """Query the API for per-job durations of a workflow run."""
    raw = run_gh(
        "api", f"repos/{{owner}}/{{repo}}/actions/runs/{run_id}/jobs",
        "--paginate", "--jq",
        ".jobs[] | {name, started_at, completed_at, status, conclusion}",
        repo=repo,
    )
    jobs = []
    for line in raw.strip().splitlines():
        if not line.strip():
            continue
        j = json.loads(line)
        if not j.get("started_at") or not j.get("completed_at"):
            continue
        start = parse_ts(j["started_at"])
        end = parse_ts(j["completed_at"])
        dur = (end - start).total_seconds()
        jobs.append({
            "name": j["name"],
            "status": j.get("conclusion", j.get("status", "?")),
            "duration_s": dur,
        })
    jobs.sort(key=lambda j: j["duration_s"], reverse=True)
    return jobs


# ── download & extract logs ─────────────────────────────────────────────────

def download_logs(run_id: int, dest_dir: Path, repo: str = "") -> Path:
    """Download and extract workflow run logs into *dest_dir*/<run_id>/."""
    run_dir = dest_dir / str(run_id)
    if run_dir.exists() and any(run_dir.glob("*.txt")):
        return run_dir  # already cached
    run_dir.mkdir(parents=True, exist_ok=True)
    zip_path = run_dir / "logs.zip"
    # gh api writes binary to stdout; bypass run_gh to avoid text decoding
    result = subprocess.run(
        ["gh", "api",
         f"repos/{repo}/actions/runs/{run_id}/logs",
         "-H", "Accept: application/vnd.github+json"],
        capture_output=True, check=True,
    )
    zip_path.write_bytes(result.stdout)
    with zipfile.ZipFile(zip_path) as zf:
        # Validate paths to prevent zip-slip attacks.
        for member in zf.namelist():
            target = (run_dir / member).resolve()
            if not str(target).startswith(str(run_dir.resolve())):
                raise ValueError(
                    f"Zip entry {member!r} would extract outside {run_dir}")
        zf.extractall(run_dir)
    return run_dir


# ── main analysis ───────────────────────────────────────────────────────────

def analyse_run(run_id: int, log_dir: Path, top: int,
                repo: str = "") -> dict:
    """Analyse a single workflow run. Returns a summary dict."""
    info(f"\n{'=' * 72}")
    info(f"  Run {run_id}")
    info(f"{'=' * 72}")

    # 1. Job-level durations from API
    jobs = get_job_durations(run_id, repo=repo)
    info(f"\n  Jobs (sorted by duration):")
    for j in jobs:
        info(f"    {fmt_duration(j['duration_s']):>12s}  "
              f"[{j['status']:>7s}]  {j['name']}")

    # 2. Download logs and do step/test analysis for top jobs
    try:
        run_dir = download_logs(run_id, log_dir, repo=repo)
    except Exception as e:
        info(f"  [warn] Could not download logs: {e}")
        return {"run_id": run_id, "jobs": jobs, "details": {}}

    details = {}
    log_files = sorted(run_dir.glob("*.txt"))
    # Map log files to job names (files are like "4_check-macos-14-cmake-clang.txt")
    log_map: dict[str, Path] = {}
    for lf in log_files:
        # Strip leading number and underscore
        name = re.sub(r"^\d+_", "", lf.stem)
        log_map[name] = lf

    for j in jobs[:top]:
        job_name = j["name"]
        # Find matching log file (fuzzy match on name)
        log_file = None
        for lname, lpath in log_map.items():
            if lname == job_name or lname.replace("-", "_") == job_name.replace("-", "_"):
                log_file = lpath
                break
        if log_file is None:
            # Try substring match
            for lname, lpath in log_map.items():
                if job_name.replace("-", "_") in lname.replace("-", "_") or \
                   lname.replace("-", "_") in job_name.replace("-", "_"):
                    log_file = lpath
                    break
        if log_file is None:
            continue

        lines = log_file.read_text(errors="replace").splitlines()

        info(f"\n  ── {job_name} ({fmt_duration(j['duration_s'])}) ──")

        # Steps
        steps = parse_steps(lines)
        if steps:
            info(f"    Steps:")
            for s in sorted(steps, key=lambda s: s["duration_s"],
                            reverse=True):
                label = s["name"][:70]
                info(f"      {fmt_duration(s['duration_s']):>10s}  {label}")

        # Tests (ctest or make)
        ctest_tests = parse_ctest(lines)
        make_suites = parse_make_suites(lines)
        individual_tests = parse_individual_tests(lines)

        if ctest_tests:
            info(f"    Slowest ctest tests:")
            for t in ctest_tests[:15]:
                info(f"      {fmt_duration(t['duration_s']):>10s}  "
                      f"[{t['status']}]  {t['name']}")
            total_match = None
            for line in lines:
                m = _CTEST_TOTAL_RE.search(line)
                if m:
                    total_match = float(m.group(1))
            if total_match:
                info(f"    Total ctest time: {fmt_duration(total_match)}")

        # Show individual tests within the slowest ctest suites
        if individual_tests:
            # Pick suites that took > 60s at the ctest level
            slow_suites = [t["name"] for t in ctest_tests
                           if t["duration_s"] > 60]
            # Also include slow make suites
            slow_suites += [s["name"] for s in make_suites
                            if s["duration_s"] > 60]
            shown = set()
            for suite in slow_suites[:8]:
                if suite in shown:
                    continue
                shown.add(suite)
                itests = individual_tests.get(suite, [])
                if not itests:
                    continue
                info(f"    Individual tests in {suite}:")
                for it in itests[:10]:
                    info(f"        {fmt_duration(it['duration_s']):>8s}"
                          f"  {it['name']}")

        if make_suites:
            info(f"    Slowest make test suites:")
            for s in make_suites[:15]:
                info(f"      {fmt_duration(s['duration_s']):>10s}  {s['name']}")

        details[job_name] = {
            "steps": steps,
            "ctest_tests": ctest_tests,
            "make_suites": make_suites,
            "individual_tests": individual_tests,
        }

    return {"run_id": run_id, "jobs": jobs, "details": details}


def _stats(durs: list[float]) -> str:
    """``<median> (med) · <min>–<max> · n=<count>`` for a list of durations."""
    if not durs:
        return "n=0"
    return (f"{fmt_duration(median(durs))} (med) · "
            f"{fmt_duration(min(durs))}–{fmt_duration(max(durs))} · "
            f"n={len(durs)}")


def _slowest_job_per_run(result: dict) -> tuple[str, float]:
    """Return (name, duration_s) of the slowest job in a single run."""
    jobs = [j for j in result.get("jobs", []) if j.get("duration_s", 0) > 0]
    if not jobs:
        return ("(none)", 0.0)
    j = max(jobs, key=lambda j: j["duration_s"])
    return (j["name"], j["duration_s"])


def _critical_paths(results: list[dict]) -> dict[str, dict]:
    """Per job, summarise the serial critical path across runs.

    For a job whose tests run as ctest suites under ``-jN``, the wall-clock is
    bounded below by the *longest single suite* (which cannot be parallelised)
    and by ``sum_of_suites / N``.  We therefore report, per job, the suite with
    the greatest median duration across runs (with its name and that median),
    and the median of the per-run suite totals.  Selecting the suite by its
    median keeps the reported name and figure consistent even when the slowest
    suite differs from run to run.  A job whose longest-suite median is a large
    fraction of its total is a parallelism bottleneck that splitting the suite
    would help.
    """
    # Per job: suite name -> that suite's durations across the analysed runs.
    per_suite: dict[str, dict[str, list[float]]] = defaultdict(
        lambda: defaultdict(list))
    total: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for job_name, detail in r.get("details", {}).items():
            suites = detail.get("ctest_tests", [])
            if not suites:
                continue
            for s in suites:
                per_suite[job_name][s["name"]].append(s["duration_s"])
            total[job_name].append(sum(s["duration_s"] for s in suites))
    out: dict[str, dict] = {}
    for job_name, suites in per_suite.items():
        top_name = max(suites, key=lambda n: median(suites[n]))
        out[job_name] = {
            "longest_med": median(suites[top_name]),
            "longest_suite": top_name,
            "total_med": median(total[job_name]),
            "n": len(total[job_name]),
        }
    return out


def print_cross_run_summary(results: list[dict], top: int):
    """Print aggregated summary across all analysed runs."""
    info(f"\n{'#' * 72}")
    info(f"  CROSS-RUN SUMMARY ({len(results)} runs)")
    info(f"{'#' * 72}")

    # Aggregate job durations
    job_durations: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for j in r["jobs"]:
            job_durations[j["name"]].append(j["duration_s"])

    # Per-run trend (most recent first): slowest job per run over time.
    if any("created" in r for r in results):
        info(f"\n  Run trend (most recent first):")
        for r in sorted(results, key=lambda r: r.get("created", ""),
                        reverse=True):
            name, dur = _slowest_job_per_run(r)
            date = (r.get("created", "") or "")[:16].replace("T", " ")
            info(f"    {date}  {r.get('sha',''):10s}  "
                  f"[{r.get('conclusion','?'):>9s}]  "
                  f"slowest: {fmt_duration(dur):>10s}  {name}")

    info(f"\n  Job durations (sorted by median):")
    sorted_jobs = sorted(job_durations.items(),
                         key=lambda kv: median(kv[1]), reverse=True)
    for name, durs in sorted_jobs:
        info(f"    {_stats(durs)}  {name}")

    # Per-job serial critical path (longest single suite bounds wall-clock).
    crit = _critical_paths(results)
    if crit:
        info(f"\n  Per-job critical path (longest serial suite, median):")
        for job_name, c in sorted(crit.items(),
                                  key=lambda kv: kv[1]["longest_med"],
                                  reverse=True):
            info(f"    {fmt_duration(c['longest_med']):>10s}  "
                  f"(of {fmt_duration(c['total_med'])} total)  "
                  f"{job_name}: {c['longest_suite']}")

    # Aggregate ctest test durations
    test_durations: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for job_name, detail in r.get("details", {}).items():
            for t in detail.get("ctest_tests", []):
                key = f"{job_name} / {t['name']}"
                test_durations[key].append(t["duration_s"])

    if test_durations:
        info(f"\n  Slowest individual ctest tests (by median, across runs):")
        sorted_tests = sorted(test_durations.items(),
                              key=lambda kv: median(kv[1]),
                              reverse=True)
        for name, durs in sorted_tests[:top]:
            info(f"    {_stats(durs)}  {name}")

    # Aggregate make suite durations
    suite_durations: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for job_name, detail in r.get("details", {}).items():
            for s in detail.get("make_suites", []):
                key = f"{job_name} / {s['name']}"
                suite_durations[key].append(s["duration_s"])

    if suite_durations:
        info(f"\n  Slowest make test suites (by median, across runs):")
        sorted_suites = sorted(suite_durations.items(),
                               key=lambda kv: median(kv[1]),
                               reverse=True)
        for name, durs in sorted_suites[:top]:
            info(f"    {_stats(durs)}  {name}")

    # Aggregate individual tests within ctest suites
    indiv_durations: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for job_name, detail in r.get("details", {}).items():
            for suite, tests in detail.get("individual_tests", {}).items():
                for t in tests:
                    key = f"{job_name} / {suite} / {t['name']}"
                    indiv_durations[key].append(t["duration_s"])

    if indiv_durations:
        info(f"\n  Slowest individual tests within ctest suites "
              f"(by median, across runs):")
        sorted_indiv = sorted(indiv_durations.items(),
                              key=lambda kv: median(kv[1]),
                              reverse=True)
        for name, durs in sorted_indiv[:top]:
            info(f"    {_stats(durs)}  {name}")


def generate_markdown_summary(results: list[dict], top: int = 20) -> str:
    """Generate a Markdown summary suitable for GitHub Actions job summaries."""
    lines: list[str] = []
    w = lines.append

    w(f"# CI Performance Analysis ({len(results)} runs)\n")
    w("Figures are **medians across runs** (robust to the large run-to-run "
      "variance of, in particular, the macOS runners). Only post-merge runs "
      "on the target branch are analysed, including failed/timed-out ones.\n")

    # Per-run trend: shows the slowest job per run over time, so a genuine
    # upward trend is distinguishable from one-off slow runs.
    have_meta = any("created" in r for r in results)
    if have_meta:
        w("## Run trend (most recent first)\n")
        w("| Date | Commit | Result | Slowest job | Duration |")
        w("|------|--------|--------|-------------|----------|")
        for r in sorted(results, key=lambda r: r.get("created", ""),
                        reverse=True):
            name, dur = _slowest_job_per_run(r)
            date = (r.get("created", "") or "")[:16].replace("T", " ")
            w(f"| {date} | {r.get('sha','')} | {r.get('conclusion','?')} "
              f"| {name} | {fmt_duration(dur)} |")
        w("")

    # Job durations table (median-based).
    job_durations: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for j in r["jobs"]:
            job_durations[j["name"]].append(j["duration_s"])

    w("## Slowest jobs (median)\n")
    w("| Job | Median | Min | Max | Runs |")
    w("|-----|--------|-----|-----|------|")
    sorted_jobs = sorted(job_durations.items(),
                         key=lambda kv: median(kv[1]), reverse=True)
    for name, durs in sorted_jobs[:top]:
        w(f"| {name} | {fmt_duration(median(durs))} "
          f"| {fmt_duration(min(durs))} | {fmt_duration(max(durs))} "
          f"| {len(durs)} |")

    # Per-job serial critical path: the longest single suite bounds wall-clock
    # under -jN, so this highlights where splitting a suite would help.
    crit = _critical_paths(results)
    if crit:
        w("\n## Per-job critical path (longest serial suite)\n")
        w("A job's wall-clock is bounded below by its longest single suite "
          "(cannot be parallelised) and by Σsuites / parallelism. A longest "
          "suite that is a large share of Σsuites is a split candidate.\n")
        w("| Job | Longest suite (median) | Suite | Σ suites (median) |")
        w("|-----|------------------------|-------|-------------------|")
        for job_name, c in sorted(crit.items(),
                                  key=lambda kv: kv[1]["longest_med"],
                                  reverse=True)[:top]:
            w(f"| {job_name} | {fmt_duration(c['longest_med'])} "
              f"| {c['longest_suite']} | {fmt_duration(c['total_med'])} |")

    # Slowest ctest suites (median).
    test_durations: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for job_name, detail in r.get("details", {}).items():
            for t in detail.get("ctest_tests", []):
                key = f"{job_name} / {t['name']}"
                test_durations[key].append(t["duration_s"])

    if test_durations:
        w("\n## Slowest test suites (ctest, median)\n")
        w("| Job / Suite | Median | Min | Max | Runs |")
        w("|-------------|--------|-----|-----|------|")
        sorted_tests = sorted(test_durations.items(),
                              key=lambda kv: median(kv[1]), reverse=True)
        for name, durs in sorted_tests[:top]:
            w(f"| {name} | {fmt_duration(median(durs))} "
              f"| {fmt_duration(min(durs))} | {fmt_duration(max(durs))} "
              f"| {len(durs)} |")

    # Slowest individual tests (median).
    indiv_durations: dict[str, list[float]] = defaultdict(list)
    for r in results:
        for job_name, detail in r.get("details", {}).items():
            for suite, tests in detail.get("individual_tests", {}).items():
                for t in tests:
                    key = f"{job_name} / {suite} / {t['name']}"
                    indiv_durations[key].append(t["duration_s"])

    if indiv_durations:
        w("\n## Slowest individual tests (median)\n")
        w("| Job / Suite / Test | Median | Min | Max | Runs |")
        w("|--------------------|--------|-----|-----|------|")
        sorted_indiv = sorted(indiv_durations.items(),
                              key=lambda kv: median(kv[1]), reverse=True)
        for name, durs in sorted_indiv[:top]:
            w(f"| {name} | {fmt_duration(median(durs))} "
              f"| {fmt_duration(min(durs))} | {fmt_duration(max(durs))} "
              f"| {len(durs)} |")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Analyse CI run durations for diffblue/cbmc")
    parser.add_argument(
        "--runs", type=int, default=5,
        help="Number of recent completed runs to analyse (default: 5)")
    parser.add_argument(
        "--workflow", default="pull-request-checks.yaml",
        help="Workflow name or filename to analyse "
             "(default: 'pull-request-checks.yaml')")
    parser.add_argument(
        "--branch", default="develop",
        help="Only analyse runs on this branch (default: 'develop'). "
             "Pass an empty string to disable branch filtering.")
    parser.add_argument(
        "--event", default="push",
        help="Only analyse runs triggered by this event (default: 'push', "
             "i.e. post-merge runs on the target branch rather than noisier "
             "pull_request runs). Pass an empty string to disable filtering.")
    parser.add_argument(
        "--all-workflows", action="store_true",
        help="Analyse all workflows, not just the specified one")
    parser.add_argument(
        "--repo", default="diffblue/cbmc",
        help="GitHub repository (default: diffblue/cbmc)")
    parser.add_argument(
        "--top", type=int, default=20,
        help="Number of top items to show in summaries (default: 20)")
    parser.add_argument(
        "--log-dir", default=None,
        help="Directory to cache downloaded logs (default: temp dir)")
    parser.add_argument(
        "--markdown", action="store_true",
        help="Output a Markdown summary (for GitHub Actions job summaries)")
    parser.add_argument(
        "--quiet", "-q", action="store_true",
        help="Suppress verbose progress output (only print markdown if "
             "--markdown is given)")
    args = parser.parse_args()
    repo = args.repo

    global _quiet
    _quiet = args.quiet

    # When --log-dir is given, keep logs for reuse; otherwise use a
    # temporary directory that is cleaned up automatically on exit.
    tmp_ctx = None
    if args.log_dir:
        log_dir = Path(args.log_dir)
    else:
        tmp_ctx = tempfile.TemporaryDirectory(prefix="cbmc-ci-logs-")
        log_dir = Path(tmp_ctx.name)
    info(f"Log cache directory: {log_dir}")

    try:
        _run_analysis(args, repo, log_dir)
    finally:
        if tmp_ctx is not None:
            tmp_ctx.cleanup()


def _run_analysis(args: argparse.Namespace, repo: str, log_dir: Path):
    """Core analysis logic, separated for clean temp-dir management."""
    # Discover workflows to analyse
    if args.all_workflows:
        raw = run_gh(
            "run", "list", "--limit", "100",
            "--json", "workflowName",
            "--jq", ".[].workflowName",
            repo=repo,
        )
        workflows = sorted(set(raw.strip().splitlines()))
    else:
        workflows = [args.workflow]

    all_results = []

    for wf in workflows:
        info(f"\n{'*' * 72}")
        info(f"  Workflow: {wf}")
        info(f"{'*' * 72}")

        # Select the most recent *completed* runs. By default we restrict to
        # post-merge runs on the target branch (push to develop): pull_request
        # runs execute on a throw-away merge commit, run far more often, and
        # are noisier, so mixing them in obscures the develop trend. We also
        # deliberately include failed/timed-out runs (not just successes) --
        # those are exactly the runs a performance investigation cares about.
        list_args = ["run", "list", "--limit", "100", "--workflow", wf]
        if args.branch:
            list_args += ["--branch", args.branch]
        if args.event:
            list_args += ["--event", args.event]
        list_args += [
            "--json", "databaseId,status,conclusion,headSha,createdAt",
            "--jq",
            r'.[] | select(.status == "completed") '
            r'| "\(.databaseId)\t\(.conclusion)\t\(.headSha[0:10])\t\(.createdAt)"',
        ]
        raw = run_gh(*list_args, repo=repo)

        run_meta = []
        for line in raw.strip().splitlines():
            if not line.strip():
                continue
            parts = line.split("\t")
            run_meta.append({
                "id": int(parts[0]),
                "conclusion": parts[1] if len(parts) > 1 else "?",
                "sha": parts[2] if len(parts) > 2 else "",
                "created": parts[3] if len(parts) > 3 else "",
            })
        run_meta = run_meta[:args.runs]

        if not run_meta:
            info("  No completed runs found "
                 f"(branch={args.branch or 'any'}, event={args.event or 'any'}).")
            continue

        info(f"  Analysing runs: {[m['id'] for m in run_meta]}")

        for meta in run_meta:
            result = analyse_run(meta["id"], log_dir, top=args.top, repo=repo)
            result["conclusion"] = meta["conclusion"]
            result["sha"] = meta["sha"]
            result["created"] = meta["created"]
            all_results.append(result)

    if all_results:
        print_cross_run_summary(all_results, top=args.top)
        if args.markdown:
            md = generate_markdown_summary(all_results, top=args.top)
            print(md)

    info("\nDone.")


if __name__ == "__main__":
    main()
