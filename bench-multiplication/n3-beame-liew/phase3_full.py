#!/usr/bin/env python3
"""
N3 Phase 3 full proof: compose per-strip BP DRATs into a single
proof of multiplier commutativity.

For each k in [1, 2n-1]:
  - Build strip CNF (phi_Strip(k)) via extract_strip + forced_e.
  - Build BP + emit DRAT (via v9 style).

Then compose: the strip DRAT refutes phi_Strip(k) = strip_clauses
+ forced_e units. The full formula is the full CNF (not strip),
with diff OR clause at the root.

Outer resolution: for each k, the strip's forced_e contributes
diff[i] = F for i < k, diff[k] = T. Outside the strip, these
are assumptions. The strip's empty clause (from v9) is derived
assuming these forced literals.

To compose: for each k, convert strip DRAT clauses to full-CNF
DRAT by adding the assumed diff literals to each clause (weakening).
Then UP with the original diff OR clause (at least one diff is
true) lets us drive the full refutation.

For this first version, we emit per-strip DRAT inline and rely
on the strip CNF being a subset of the full CNF (which it is).
"""

import os
import sys
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_bp, build_strip_all, propagate,
)
from phase3_strip_extract import strip_delta
from generate_array_mul_comm_meta import build_commutativity_cnf_meta
from phase3_bp_drat_v9 import emit_tree_post_order


def compose_full_proof(n, out_cnf, out_drat):
    """Emit full CNF and composed DRAT proof."""
    cnf, _, _, _, _ = build_commutativity_cnf_meta(n)
    all_clauses = list(cnf.clauses)

    # Find diff vars.
    diff_vars = sorted(
        [v for v, r in cnf.meta.items() if r and r[0] == "diff"],
        key=lambda v: cnf.meta[v][1]
    )

    max_var = cnf.next_var - 1
    with open(out_cnf, "w") as f:
        f.write(f"p cnf {max_var} {len(all_clauses)}\n")
        for cl in all_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    # Emit composed DRAT.
    with open(out_drat, "w") as out:
        # First, emit tableau symmetry clauses as RUP lemmas.
        # These are RUP-derivable from the AND gate clauses
        # (commutativity of AND).
        pp_c_vars = {}
        pp_d_vars = {}
        for v, role in cnf.meta.items():
            if role and role[0] == "pp_c":
                pp_c_vars[(role[1], role[2])] = v
            elif role and role[0] == "pp_d":
                pp_d_vars[(role[1], role[2])] = v

        for (i, j), cv in pp_c_vars.items():
            dv_key = (j, i)
            if dv_key in pp_d_vars:
                dv = pp_d_vars[dv_key]
                if cv == dv:
                    continue
                # Emit -cv, dv (cv -> dv)
                out.write(f"{-cv} {dv} 0\n")
                # Emit cv, -dv (dv -> cv)
                out.write(f"{cv} {-dv} 0\n")
        # For each k in [1, 2n-1]: emit the strip's BP DRAT,
        # but each clause weakened by adding the diff literals:
        #   -diff[i] for i < k (assumption diff[i] = F)
        #   +diff[k] (assumption diff[k] = T)
        # ... wait, we assume diff[i]=F gives -diff[i] as unit.
        # Each emitted strip clause C holds under "diff[i]=F for i<k,
        # diff[k]=T". To make C valid in the full proof (without
        # those assumptions), we need to add the NEGATIONS:
        #   +diff[i] for i < k (would make assumption wrong)
        #   -diff[k]
        # So each full-proof clause = C + {diff[i]: i<k} + {-diff[k]}.
        # The FINAL empty clause becomes {diff[i]: i<k, -diff[k]}.
        #
        # Then we'll have 2n-1 such "nearly-empty" clauses, one per k.
        # Resolve them with the "diff OR" clause (at least one diff
        # is True) to derive empty.

        # Actually simpler: after all strip proofs are emitted and
        # we have (for each k) the "conditional empty" clause
        # {diff[i]: i<k, -diff[k]}, resolve them pairwise with
        # the diff OR clause to get empty.

        # Rewrite each strip clause C as:
        #   C + {diff[i]: i<k} + {-diff[k]}
        # Each is RUP-valid because: under these assumptions,
        # strip's UP derives C (from the strip CNF).

        strip_sizes = []
        for k in range(0, 2*n):
            cnf_s, strip_clauses, forced_e, delta = build_strip_all(n, k)

            # Extra literals to add to each strip clause to make it
            # valid in the FULL CNF (not assuming forced_e).
            # forced_e: diff[i]=False for i<k (unit -diff[i]),
            #           diff[k]=True (unit +diff[k]).
            # To cancel a unit -diff[i], add +diff[i] to every clause.
            # To cancel +diff[k], add -diff[k] to every clause.
            extras = set()
            for i, dv in enumerate(diff_vars):
                if i < k:
                    extras.add(dv)
                elif i == k:
                    extras.add(-dv)
                # i > k: diff[i] is free, no cancellation needed.

            # Build BP and get clauses.
            _, _, _, branch_order, bp = build_bp(n, k)

            # Emit the strip's v9 DRAT, but with `extras` added to
            # each clause.
            class WeakenedWriter:
                def __init__(self, f, extras):
                    self.f = f
                    self.extras = extras
                    self.count = 0
                def write(self, s):
                    # Parse each clause line from s, add extras.
                    for line in s.split("\n"):
                        line = line.strip()
                        if not line:
                            continue
                        lits = [int(x) for x in line.split()][:-1]  # drop trailing 0
                        weakened = frozenset(lits) | self.extras
                        sorted_lits = sorted(weakened, key=lambda x: (abs(x), x))
                        if sorted_lits:
                            self.f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                        else:
                            self.f.write("0\n")
                        self.count += 1

            ww = WeakenedWriter(out, extras)
            emit_tree_post_order(bp, strip_clauses, ww)
            strip_sizes.append(ww.count)

        # After all strips, the weakened empty clauses are:
        #   nearly_k = {diff[i]: i<k} U {-diff[k]}
        # These are in the proof already (as the last lemma of each
        # strip).
        #
        # Now we progressively derive {-diff[i]} as unit clauses:
        #   -diff[0] is already emitted (nearly_0 = {-diff[0]}).
        #   -diff[1] follows from nearly_1 + {-diff[0]} by UP.
        #     (nearly_1 = {+diff[0], -diff[1]}; with diff[0]=F, get -diff[1].)
        #   -diff[2] follows from nearly_2 + {-diff[0], -diff[1]} by UP.
        #   ...
        # Each {-diff[k]} is RUP-derivable from the accumulated proof.

        for k in range(1, 2*n):
            # Emit {-diff[k]} as a RUP lemma.
            out.write(f"{-diff_vars[k]} 0\n")

        # Now UP on diff_or clause + all {-diff[i]} = empty. Emit.
        out.write("0\n")

    return strip_sizes


def main():
    if len(sys.argv) != 2:
        print("usage: phase3_full.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])

    cnf_path = f"/tmp/phase3_full_n{n}.cnf"
    drat_path = f"/tmp/phase3_full_n{n}.drat"

    strip_sizes = compose_full_proof(n, cnf_path, drat_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}: CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")
    print(f"  strip sizes: {strip_sizes}")

    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=600,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
