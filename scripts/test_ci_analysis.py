"""Unit tests for the pure helper functions in ci_analysis.py.

The bulk of ci_analysis.py is I/O-bound on the ``gh`` CLI and not unit-tested
here, but the aggregation helpers (``median``, ``_stats``,
``_slowest_job_per_run``, ``_critical_paths``) are pure functions over plain
dicts/lists and are worth pinning down.

Run with::

    python3 -m pytest scripts/test_ci_analysis.py

(or simply ``python3 scripts/test_ci_analysis.py``).
"""

import os
import sys

# Make ``import ci_analysis`` work regardless of the working directory pytest
# is invoked from.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import ci_analysis as ci  # noqa: E402


def test_median_odd():
    assert ci.median([3, 1, 2]) == 2


def test_median_even():
    assert ci.median([1, 2, 3, 4]) == 2.5


def test_median_single():
    assert ci.median([7]) == 7


def test_median_empty_is_zero():
    # The 0.0-for-empty behaviour is relied on by _stats/_critical_paths.
    assert ci.median([]) == 0.0


def test_stats_empty():
    assert ci._stats([]) == "n=0"


def test_stats_reports_count_and_median():
    s = ci._stats([60, 120, 180])
    assert "n=3" in s
    assert "(med)" in s


def test_slowest_job_per_run_empty():
    assert ci._slowest_job_per_run({"jobs": []}) == ("(none)", 0.0)


def test_slowest_job_per_run_picks_max():
    result = {"jobs": [
        {"name": "a", "duration_s": 10},
        {"name": "b", "duration_s": 30},
        {"name": "c", "duration_s": 20},
    ]}
    assert ci._slowest_job_per_run(result) == ("b", 30)


def _run(suites):
    """A minimal run dict carrying one job's ctest suite durations."""
    return {"details": {"job": {"ctest_tests": suites}}}


def test_critical_path_name_matches_reported_median():
    # Suite X is slowest in run 1 and suite Y in run 2, but X has the larger
    # median across both runs. The reported suite name must therefore be X and
    # the reported median must be X's median -- i.e. name and figure stay
    # consistent even when the per-run slowest suite differs.
    run1 = _run([{"name": "X", "duration_s": 100},
                 {"name": "Y", "duration_s": 10}])
    run2 = _run([{"name": "X", "duration_s": 90},
                 {"name": "Y", "duration_s": 95}])
    cp = ci._critical_paths([run1, run2])["job"]
    assert cp["longest_suite"] == "X"
    assert cp["longest_med"] == 95            # median(100, 90)
    assert cp["total_med"] == ci.median([110, 185])
    assert cp["n"] == 2


def test_critical_path_ignores_jobs_without_ctest_suites():
    runs = [{"details": {"job": {"ctest_tests": []}}}]
    assert ci._critical_paths(runs) == {}


if __name__ == "__main__":
    sys.exit(__import__("pytest").main([__file__, "-v"]))
