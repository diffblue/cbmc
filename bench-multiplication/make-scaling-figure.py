#!/usr/bin/env python3
"""Generate Figure: Gröbner-basis scaling on binomial and variables-scaling families.

Replaces Tables 4 and 5 in paper.tex §3.3.

Methodology (consistent with §2.7 Table 2): median of 4 warm runs
(5 runs total, first discarded). CBMC smt2_solver --cadical
--multiplier-encoding comba-cs.
"""

import subprocess
import time
import statistics
import sys
from pathlib import Path

import matplotlib
matplotlib.use("pdf")
import matplotlib.pyplot as plt


def time_run(cmd, runs=5, timeout=120):
    times = []
    for i in range(runs):
        t = time.perf_counter()
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None
        elapsed = time.perf_counter() - t
        if "unsat" not in r.stdout:
            return None
        times.append(elapsed)
    return statistics.median(times[1:]) * 1000


def measure_binomial():
    data = {8: [], 16: []}
    for bw in [8, 16]:
        for k in range(2, 7):
            bench = f"bench-multiplication/degree-scaling/binomial_deg{k}_bw{bw}.smt2"
            t = time_run(["build/bin/smt2_solver", "--cadical", bench,
                          "--multiplier-encoding", "comba-cs"])
            data[bw].append(t)
    return data


def measure_varscale():
    data = []
    for k in range(2, 7):
        bench = f"bench-multiplication/variables-scaling/varscale_k{k}_bw16.smt2"
        t = time_run(["build/bin/smt2_solver", "--cadical", bench,
                      "--multiplier-encoding", "comba-cs"])
        data.append(t)
    return data


def main():
    print("Measuring binomial scaling…", file=sys.stderr)
    binomial = measure_binomial()
    print(f"  BW=8: {binomial[8]}", file=sys.stderr)
    print(f"  BW=16: {binomial[16]}", file=sys.stderr)

    print("Measuring variables scaling…", file=sys.stderr)
    varscale = measure_varscale()
    print(f"  varscale: {varscale}", file=sys.stderr)

    ks = list(range(2, 7))

    fig, axes = plt.subplots(1, 2, figsize=(7.0, 2.7))

    # Panel (a): degree-scaling
    ax = axes[0]
    ax.semilogy(ks, binomial[8], "o-", label="BW = 8", linewidth=1.4, markersize=4)
    ax.semilogy(ks, binomial[16], "s-", label="BW = 16", linewidth=1.4, markersize=4)
    ax.set_xlabel("polynomial degree $k$")
    ax.set_ylabel("solver time (ms)")
    ax.set_title("(a) Binomial identity $(a+b)^k$")
    ax.set_xticks(ks)
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
    ax.legend(loc="lower right", fontsize=8)
    ax.set_ylim(1, 100)

    # Panel (b): variables-scaling
    ax = axes[1]
    ax.semilogy(ks, varscale, "^-", color="tab:red", linewidth=1.4, markersize=4,
                label="$\\sum_{\\sigma \\in S_k} \\prod x_{\\sigma(i)}$ at BW=16")
    ax.set_xlabel("number of variables $k$")
    ax.set_ylabel("solver time (ms)")
    ax.set_title("(b) Permutation identity")
    ax.set_xticks(ks)
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
    ax.legend(loc="lower right", fontsize=8)
    ax.set_ylim(1, 10000)

    plt.tight_layout()

    out_path = Path(__file__).parent.parent / "doc" / "paper-algebraic" / "scaling-figure.pdf"
    plt.savefig(out_path, bbox_inches="tight")
    print(f"Saved {out_path}", file=sys.stderr)

    # Also write data to TSV for the paper artifact
    tsv_path = Path(__file__).parent.parent / "doc" / "paper-algebraic" / "data" / "scaling-figure.tsv"
    with open(tsv_path, "w") as f:
        f.write("# Binomial scaling and variables-scaling data\n")
        f.write("# Median of 4 warm runs (5 total, first discarded), ms\n")
        f.write("benchmark\tk\ttime_ms\n")
        for bw in [8, 16]:
            for k, t in zip(ks, binomial[bw]):
                f.write(f"binomial_deg{k}_bw{bw}\t{k}\t{t:.2f}\n")
        for k, t in zip(ks, varscale):
            f.write(f"varscale_k{k}_bw16\t{k}\t{t:.2f}\n")
    print(f"Saved {tsv_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
