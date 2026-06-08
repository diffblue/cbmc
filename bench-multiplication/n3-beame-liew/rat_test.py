#!/usr/bin/env python3
"""
Option A: verify drat-trim accepts RAT lemmas introducing extension
variables.

Base CNF (UNSAT, four 2-literal clauses covering every (x1, x2)):
  C1: x1 OR x2
  C2: -x1 OR x2
  C3: x1 OR -x2
  C4: -x1 OR -x2

Proof strategy -- structured so drat-trim MUST check the RAT
lemmas (i.e. they are in the proof core, not dead code):

  L1 (RAT on -3): (-3 1)
  L2 (RAT on -3): (-3 2)
  L3 (RAT on  3): (3 -1 -2)

  L4 (RUP):      (-3)          -- derivable: assume x3=T; L1,L2 force
                                  x1=x2=T; C4 falsified.
  L5 (RUP):      (3)           -- derivable: assume x3=F; L3 reduces
                                  to (-1 -2) = C4; combined with C1-C4
                                  trivially UNSAT? Let's compute:
                                  we have -3 assumed, so L1 and L2
                                  are satisfied. L3 = (-1 -2). The
                                  base has C1 = (1 2). Resolving
                                  on either var gives a single
                                  literal, but via UP alone it
                                  requires branch -- *not* RUP-
                                  derivable. So L5 won't work; we
                                  need a different tail.

Let's instead:
  After L4 (unit -3), UP on L3 (3 -1 -2) with x3=F gives (-1 -2),
  a new binary clause (falsifiable by one (x1,x2) assignment).
  Not directly a unit. So we need another chain.

Alternative: after L4 (unit -3), we go back to proving (2) and
(-2) from the original CNF (which doesn't actually need x3), then
empty.

  L5 (RUP):      (2)            -- assume -x2; UP C1 forces x1=T;
                                   C2 (-1 2) falsified by x1=T,x2=F.
                                   RUP succeeds, no x3 needed.
  L6 (RUP):      (-2)           -- assume  x2; UP C3 forces x1=T;
                                   C4 falsified. RUP succeeds.
  L7 (empty):    ()              -- via UP on L5, L6.

The only RAT-dependent lemma is L4 (its RUP derivation uses L1 and
L2). If drat-trim accepts L4, then we've confirmed RAT with
extension variables works.

To force L4 to be in the core (not skipped by backward pruning),
we need L4 to be *used* in deriving later lemmas. Add:

  L4'  (-3)
  L5'  (-3 2)   copy of L2 using L4, no new info, but makes x3
                alive in the proof.

Actually the simplest way: after L4 introduce a clause that, via RUP,
uses L4 ... but any such clause would mimic L5/L6 above. Let me try
a different tail: resolve L3 with L4 to deduce C4 as a "derived"
clause.

Actually, drat-trim's backward checking marks a lemma as "in core"
if its literal appears in the antecedent chain of a later in-core
lemma. If the proof's final empty clause can be derived via
backward chaining from L5/L6 without touching L4, L4 is not in
core and drat-trim will simply NOT CHECK its RAT-ness.

Which is fine for our purposes -- if drat-trim's output includes
some "RAT lemmas in core: K" count with K>0, we've confirmed the
mechanism. Let me try the minimal proof and look at that number.
"""

import subprocess


def write_cnf(path, num_vars, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(str(x) for x in cl) + " 0\n")


def main():
    cnf_path = "/tmp/rat_test.cnf"
    drat_path = "/tmp/rat_test.drat"

    clauses = [
        [1, 2],       # C1
        [-1, 2],      # C2
        [1, -2],      # C3
        [-1, -2],     # C4
    ]
    write_cnf(cnf_path, 2, clauses)

    # DRAT proof, constructed so that the RAT lemmas are in the proof core:
    #   L1: RAT on -3   (-3  1)       x3 -> x1
    #   L2: RAT on -3   (-3  2)       x3 -> x2
    #   L3: RAT on  3   ( 3 -1 -2)    x1 & x2 -> x3
    #   L4: RUP ( 3  2) -- uses L3 and C1: assume -3, -2; L3 gives -1; C1 falsified by -1,-2.
    #   L5: RUP (-3)    -- uses L1, L2, C4: assume 3; L1,L2 force x1=x2=T; C4 falsified.
    #   L6: RUP ( 2)    -- uses L5 and L4: assume -2; L5 is already unit -3; L4 (3 2) with -3, -2 = FALSE. Contradiction.
    #   L7: RUP (-2)    -- uses C3, C4: assume 2; C3 forces x1=T; C4 falsified.
    #   L8: empty       -- UP on L6, L7.
    # Core backward chain from L8: L8 needs L6 and L7; L6 needs L5 and L4;
    # L5 needs L1, L2; L4 needs L3. So L1, L2, L3 are all in core.
    with open(drat_path, "w") as f:
        f.write("-3 1 0\n")        # L1 RAT on -3
        f.write("-3 2 0\n")        # L2 RAT on -3
        f.write("3 -1 -2 0\n")     # L3 RAT on  3
        f.write("3 2 0\n")         # L4 RUP (uses L3 + C1)
        f.write("-3 0\n")          # L5 RUP (uses L1, L2, C4)
        f.write("2 0\n")           # L6 RUP (uses L5, L4)
        f.write("-2 0\n")          # L7 RUP (uses C3, C4)
        f.write("0\n")             # L8 empty (uses L6, L7)

    # Run drat-trim.
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True,
    )
    print("=== drat-trim output ===")
    print(result.stdout)
    if result.returncode != 0:
        print("STDERR:", result.stderr)
    print(f"returncode = {result.returncode}")


if __name__ == "__main__":
    main()
