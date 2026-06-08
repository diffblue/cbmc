#!/usr/bin/env python3
"""
Comprehensive scaling comparison:
- Phase 1 flat DRAT (ripple-carry)
- Phase 3 diag DRAT (ripple-carry)
- CaDiCaL raw DRAT
- CaDiCaL trimmed core
- Phase 3 diag DRAT trimmed core
- CSA flat & diag for reference

All on the same full commutativity CNF per n.
Output TSV.
"""

import os
import sys
import subprocess
import glob


CADICAL = "/home/ubuntu/cadical-src/build/cadical"
DRAT_TRIM = "/tmp/drat-trim"


def run_cmd(cmd, timeout=600):
    try:
        return subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None


def count_lemmas(path):
    if not os.path.exists(path):
        return None
    n = 0
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("d "):
                continue
            n += 1
    return n


def trim_drat(cnf_path, drat_path, core_path):
    """Run drat-trim to get core lemmas in DRAT format."""
    result = run_cmd([DRAT_TRIM, cnf_path, drat_path, "-l", core_path],
                     timeout=1200)
    if result is None:
        return None
    return count_lemmas(core_path)


def run_cadical(cnf_path, drat_path):
    """Run CaDiCaL producing DRAT proof."""
    result = run_cmd([CADICAL, cnf_path, drat_path, "--unsat"], timeout=600)
    return result


def main():
    os.chdir(os.path.dirname(os.path.abspath(__file__)))

    print("n\tphase1\tphase3_diag\tphase3_diag_core\tcadical_raw\tcadical_core")
    for n in range(3, 7):
        # Phase 1
        phase1_path = f"/tmp/comm_n{n}_bl.drat"
        phase1 = os.path.getsize(phase1_path) if os.path.exists(phase1_path) else 0

        # Phase 3 diag
        diag_path = f"/tmp/phase3_full_diag_n{n}.drat"
        diag = os.path.getsize(diag_path) if os.path.exists(diag_path) else 0
        diag_cnf = f"/tmp/phase3_full_diag_n{n}.cnf"

        # Phase 3 diag core
        diag_core_path = f"/tmp/phase3_full_diag_n{n}_core.drat"
        if os.path.exists(diag_path) and not os.path.exists(diag_core_path):
            trim_drat(diag_cnf, diag_path, diag_core_path)
        diag_core = os.path.getsize(diag_core_path) if os.path.exists(diag_core_path) else 0

        # CaDiCaL raw
        cadical_path = f"/tmp/cadical_n{n}.drat"
        if not os.path.exists(cadical_path) and os.path.exists(diag_cnf):
            # Generate the CNF if it's the same as my Phase 3 base CNF.
            # Use diag_cnf as input.
            run_cadical(diag_cnf, cadical_path)
        cadical_raw = os.path.getsize(cadical_path) if os.path.exists(cadical_path) else 0

        # CaDiCaL trimmed core
        cadical_core_path = f"/tmp/cadical_n{n}_core.drat"
        if os.path.exists(cadical_path) and not os.path.exists(cadical_core_path):
            trim_drat(diag_cnf, cadical_path, cadical_core_path)
        cadical_core = os.path.getsize(cadical_core_path) if os.path.exists(cadical_core_path) else 0

        print(f"{n}\t{phase1}\t{diag}\t{diag_core}\t{cadical_raw}\t{cadical_core}")


if __name__ == "__main__":
    main()
