#!/usr/bin/env python3
"""
Phase 3 full proof with post-generation drat-trim optimization.

Takes the output of phase3_full_diag.py and runs drat-trim -l to
extract the core lemmas (smaller DRAT file with only the lemmas
actually used in verification).

This addresses tree-unfold bloat: tree-unfolded emission emits
path-specific resolvents, many of which are redundant for the
overall proof. drat-trim's -l option identifies and keeps only
the core ones.
"""

import os
import sys
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


DRAT_TRIM = "/tmp/drat-trim"


def optimize_drat(cnf_path, drat_path, out_path):
    """Run drat-trim to extract core lemmas in DRAT format."""
    result = subprocess.run(
        [DRAT_TRIM, cnf_path, drat_path, "-l", out_path],
        capture_output=True, text=True, timeout=3600,
    )
    return result


def count_lemmas_bytes(path):
    if not os.path.exists(path):
        return 0, 0
    n = 0
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("d "):
                continue
            n += 1
    return n, os.path.getsize(path)


def main():
    if len(sys.argv) != 2:
        print("usage: phase3_full_diag_opt.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])

    cnf_path = f"/tmp/phase3_full_diag_n{n}.cnf"
    drat_path = f"/tmp/phase3_full_diag_n{n}.drat"
    opt_path = f"/tmp/phase3_full_diag_n{n}_opt.drat"

    if not os.path.exists(drat_path):
        # Generate.
        subprocess.run(
            ["python3", "phase3_full_diag.py", str(n)],
            check=True
        )

    orig_lem, orig_b = count_lemmas_bytes(drat_path)
    print(f"n={n}: original DRAT = {orig_lem} lemmas, {orig_b} bytes")

    result = optimize_drat(cnf_path, drat_path, opt_path)
    for line in result.stdout.split("\n"):
        if line.startswith("s ") or "lemmas in core" in line:
            print(f"  {line}")

    opt_lem, opt_b = count_lemmas_bytes(opt_path)
    print(f"n={n}: optimized core = {opt_lem} lemmas, {opt_b} bytes")
    print(f"  reduction: {opt_lem/orig_lem:.2f}x lemmas, "
          f"{opt_b/orig_b:.2f}x bytes")


if __name__ == "__main__":
    main()
