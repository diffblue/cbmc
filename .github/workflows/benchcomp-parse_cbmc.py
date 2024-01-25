#!/usr/bin/env python3
# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT


import json
import logging
import os
import pathlib
import re
import sys
import textwrap

import yaml


def get_description():
    return textwrap.dedent("""\
        Read CBMC statistics from a Litani run.json file.
        """)


def _get_metrics():
    return {
        "solver_runtime": {
            "pat": re.compile(r"Runtime Solver: (?P<value>[-e\d\.]+)s"),
            "parse": float,
        },
        "removed_program_steps": {
            "pat": re.compile(r"slicing removed (?P<value>\d+) assignments"),
            "parse": int,
        },
        "number_program_steps": {
            "pat": re.compile(r"size of program expression: (?P<value>\d+) steps"),
            "parse": int,
        },
        "number_vccs": {
            "pat": re.compile(
                r"Generated \d+ VCC\(s\), (?P<value>\d+) remaining after simplification"),
            "parse": int,
        },
        "symex_runtime": {
            "pat": re.compile(r"Runtime Symex: (?P<value>[-e\d\.]+)s"),
            "parse": float,
        },
        "success": {
            "pat": re.compile(r"VERIFICATION:- (?P<value>\w+)"),
            "parse": lambda v: v == "SUCCESSFUL",
        },
    }


def get_metrics():
    metrics = dict(_get_metrics())
    for _, info in metrics.items():
        for field in ("pat", "parse"):
            info.pop(field)

    # This is not a metric we return; it is used to find the correct value for
    # the number_program_steps metric
    metrics.pop("removed_program_steps", None)

    # We don't parse this directly from the output
    metrics["verification_time"] = {}

    return metrics


def get_run(root_dir):
    for fyle in pathlib.Path(root_dir).rglob("run.json"):
        with open(fyle) as handle:
            return json.load(handle)
    logging.error("No run.json found in %s", root_dir)
    sys.exit(1)


def main(root_dir):
    root_dir = pathlib.Path(root_dir)
    run = get_run(root_dir)
    metrics = _get_metrics()
    benchmarks = {}
    for pipe in run["pipelines"]:
        for stage in pipe["ci_stages"]:
            if stage["name"] != "test":
                continue
            for job in stage["jobs"]:
                if not job["wrapper_arguments"]["command"].startswith("cbmc "):
                    continue
                if "cover" in job["wrapper_arguments"]["command"]:
                    continue
                if "--show-properties" in job["wrapper_arguments"]["command"]:
                    continue

                bench_name = f"{run['project']}::{pipe['name']}"
                if not job["complete"]:
                    logging.warning(
                        "Found an incomplete CBMC benchmark '%s'",
                        bench_name)
                    continue

                benchmarks[bench_name] = {
                    "metrics": {
                        "success": job["outcome"] == "success",
                        "verification_time": float(job["duration_ms"]),
                        "solver_runtime": 0.0,
                }}

                for line in job["stdout"]:
                    for metric, metric_info in metrics.items():
                        m = metric_info["pat"].search(line)
                        if not m:
                            continue

                        parse = metric_info["parse"]
                        try:
                            # CBMC prints out some metrics more than once, e.g.
                            # "Solver" and "decision procedure". Add those
                            # values together
                            benchmarks[bench_name]["metrics"][metric] += parse(m["value"])
                        except (KeyError, TypeError):
                            benchmarks[bench_name]["metrics"][metric] = parse(m["value"])
                        break

    for bench_name, bench_info in benchmarks.items():
        try:
            n_steps = bench_info["metrics"]["number_program_steps"]
            rm_steps = bench_info["metrics"]["removed_program_steps"]
            bench_info["metrics"]["number_program_steps"] = n_steps - rm_steps
            bench_info["metrics"].pop("removed_program_steps", None)
        except KeyError:
            pass

    return {
        "metrics": get_metrics(),
        "benchmarks": benchmarks,
    }


if __name__ == "__main__":
    result = main(os.getcwd())
    print(yaml.dump(result, default_flow_style=False))
