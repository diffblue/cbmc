# Procedure-level extension: disjunctive disequalities via Rabinowitsch-on-each-branch

*Date: 2026-05-26*
*Status: **IMPLEMENTED** at commit 448bb10923 (features/adder).*
*Originally tracked here as a deferred extension; superseded by
the live implementation in `src/solvers/flattening/boolbv.cpp`.*

The original tracking notes are preserved below for context.

## Implementation result

Empirical effect on SABER's natural disjunctive form
$\bigvee_i (\text{A\_res}_i \neq \text{B\_res}_i)$ at $q = 2^{16}$:

| $N$ | Before (T/O at 60s) | After (this implementation) |
|---|---|---|
| 4 | T/O | 0.02 s |
| 8 | T/O | 0.10 s |
| 16 | T/O | 0.38 s |
| 32 | T/O | 1.54 s |
| 64 | T/O | 6.37 s |

Same speed as the per-coefficient workaround. Per-coefficient
queries (--single-coeff) still work and are kept for
fine-grained reproducibility.

## Implementation summary

In `src/solvers/flattening/boolbv.cpp`:

- Added `algebraic_disjunctive_disequalities` field
  (vector-of-vectors of equality expressions).
- `set_to()` pattern-matches `(or D1 D2 ... Dk)` where each `Di`
  is `notequal_exprt` or `not_exprt(equal_exprt(...))`. Mixed
  disjunctions (with non-disequality branches) are skipped and
  fall through to bit-blasting.
- `try_algebraic_solve()` adds a parallel loop over disjunctions:
  for each branch, runs the same per-disequality pipeline as the
  existing per-disequality loop, with vanishing-polynomial test
  first then Rabinowitsch + Buchberger. If all branches refute,
  the formula is reported UNSAT.
- The early-return gate is updated to also consider the
  disjunctive list.

A subtle detail learned during implementation: **the
vanishing-polynomial test must be replicated in each branch**.
Initially I omitted it, thinking SABER's polynomial-identity
diffs would be solved by Buchberger directly. They aren't —
they're solved by the vanishing test (the diff is literally zero
after SSA inlining, the most degenerate vanishing case). Without
the per-branch vanishing test, the per-branch Buchberger never
terminates within 30s on N=4 SABER queries.

---

## Original tracking notes (preserved for context)

## The gap

Our algebraic pre-solver in `src/solvers/flattening/boolbv.cpp`
(see `set_to` at line ~538 and the algebraic-pipeline at line ~657)
handles two assertion kinds:

1. **Equalities**: `(= e1 e2)` set to true → polynomial equation
   $e_1 - e_2 = 0$ added to the basis.

2. **Single disequalities**: `(distinct e1 e2)` set to true, or
   equivalently `(not (= e1 e2))` set to true → Rabinowitsch
   polynomial $(e_1 - e_2) \cdot e - 1 = 0$ added to the basis,
   where $e$ is a fresh witness variable.

It does **not** handle:

3. **Disjunctions of disequalities**: `(or (distinct e1 e2) (distinct e3 e4) …)`
   set to true. The disjunction structure is a SAT-level construct;
   the pre-solver currently does not pattern-match it as
   "disjunctive disequality" and just treats the assertion as a
   complex Boolean expression to bit-blast.

## Where this hurts

The natural framing of polynomial-equivalence queries with
multiple output coefficients is

```
(assert (or (distinct A_res_0 B_res_0)
            (distinct A_res_1 B_res_1)
            …
            (distinct A_res_{N-1} B_res_{N-1})))
```

i.e., "the implementations differ on at least one output
coefficient". This is the negation of the goal "they agree on
every coefficient". Examples in our experiment:

- **SABER schoolbook-vs-Karatsuba** at $N=4$: 4 output
  coefficients. The disjunctive form times out at 60 s; the
  per-coefficient workaround solves each disjunct in 0.02 s
  (4 queries, 0.08 s total).
- Any future polynomial-vector-equivalence query with $k$
  components has the same shape.

The current workaround is to mechanically split the goal into
$N$ separate per-coefficient queries and AND the results.
`bench-multiplication/saber/make-saber-query.py` supports this
via `--single-coeff`. It works but:

- Splits the procedure into $N$ separate solver invocations,
  each with its own setup overhead.
- Hides the structural unity of the goal from the procedure.
- Needs script-level orchestration (loop + AND).

## Proposed extension

When the pre-solver sees an assertion of the shape
`(or (distinct e1 e2) (distinct e3 e4) … (distinct e_{2k-1} e_{2k}))`,
treat it as a *disjunction of disequalities* rather than a
generic Boolean expression. The disjunction is unsatisfiable iff
**every** disjunct is unsatisfiable (since the disjunction has to
have at least one true disjunct).

For each disjunct $D_i = (\textit{distinct } e_{2i-1}\ e_{2i})$:

1. Construct the per-disjunct polynomial system: the existing SSA
   equalities $\cup \{(e_{2i-1} - e_{2i}) \cdot \varepsilon_i - 1 = 0\}$
   (Rabinowitsch).
2. Run Buchberger.
3. If all $i$ return UNSAT, the disjunction is unsatisfiable.
4. If any $i$ returns inconclusive, fall through to bit-blasting
   on the original assertion (do not partially-decide).

The pattern matches the per-disequality logic the pre-solver
already runs (`boolbv.cpp` around line ~787, the `single_eqs`
construction with Rabinowitsch). The new logic is simply:

- Detect the `(or (distinct …) (distinct …) …)` shape.
- Loop over disjuncts.
- AND the results.

Soundness is immediate: each branch's UNSAT proof refutes that
disjunct; no disjunct being satisfiable means no satisfying
assignment exists for the whole disjunction.

## What this would unlock

- The natural framing of SABER schoolbook-vs-Karatsuba (single
  query asserting "they differ on at least one coefficient")
  becomes solvable directly. SABER §4.8 in Paper 2 would not need
  to footnote the per-coefficient-split workaround.
- Any benchmark with multi-output polynomial equivalence becomes
  solvable in the natural framing: matrix products, polynomial-
  vector arithmetic, NTT-based multiplication equivalence, etc.
- The framework extends to nested disjunctions (`(or D1 (or D2 D3))`)
  by flattening, and to disjunctions including non-disequality
  branches by leaving non-handleable branches to bit-blasting and
  treating disequality branches via Rabinowitsch.

## What this does NOT unlock

- Conjunctions of disequalities (`(and (distinct ...) (distinct ...))`):
  these are already trivially handled — assert each disequality
  individually, run Buchberger with all Rabinowitsch polynomials
  in the same basis. (This is the current behaviour: when multiple
  disequalities are set to true, all their Rabinowitsch polynomials
  are added.)
- General Boolean structure (nested implies, ITE, etc.): out of
  scope; pattern-match only the simple disjunction-of-disequalities
  shape.

## Implementation sketch

In `boolbv.cpp::set_to`, when handling an assertion expression
set to true:

```cpp
if(!algebraic_solved && expr.id() == ID_or)
{
  // Check if every operand is a disequality (i.e., not(equal))
  bool all_disequalities = true;
  std::vector<exprt> branch_diseqs;
  for(const auto &op : expr.operands())
  {
    if(op.id() == ID_not && op.operands().size() == 1
       && op.operands()[0].id() == ID_equal)
      branch_diseqs.push_back(op.operands()[0]);
    else if(op.id() == ID_notequal && op.operands().size() == 2)
      branch_diseqs.push_back(/* rebuild as ID_equal */);
    else
    {
      all_disequalities = false;
      break;
    }
  }
  if(all_disequalities && !branch_diseqs.empty())
    algebraic_disjunctive_disequalities.push_back(branch_diseqs);
}
```

Then in the algebraic pipeline (around the
`for (const auto &diseq : algebraic_disequalities)` loop), add
a parallel loop over `algebraic_disjunctive_disequalities` that
runs Buchberger once per branch and ANDs the results.

Estimated effort: 1–2 days of careful implementation + tests.

## Tests to add

Once implemented, regression tests should cover:

1. **Direct disjunction**: a query with `(or (distinct a b) (distinct c d))`
   where both disjuncts are unsatisfiable individually
   (algebraic identity `a = b` and `c = d`); confirm the
   procedure decides UNSAT.

2. **Mixed disjunction**: one disjunct refutable, one not; confirm
   fall-through to bit-blasting (since we can't refute the whole
   disjunction).

3. **SABER per-coefficient regression**: SABER N=4
   schoolbook-vs-Karatsuba query in disjunctive form should solve
   in roughly 4× the per-coefficient time, not time out.

4. **Disjunction with extraneous branches**: `(or (distinct a b) p)`
   where `p` is a non-disequality predicate; confirm we don't
   pattern-match (because the disjunction includes a non-disequality)
   and just fall through.

## Defer rationale

Implementing this within the current Paper 2 revision cycle is
borderline:

- **Pro**: removes a real workaround, cleans up the SABER
  presentation, generally extends the procedure's coverage.
- **Con**: 1–2 days of implementation + testing; small risk of
  introducing regressions; the per-coefficient workaround already
  produces clean results.

Tracking it here so the next revision (or follow-up paper) has a
clear implementation pointer; left unimplemented for now.

## Files referenced

- `src/solvers/flattening/boolbv.cpp` — pre-solver entry point.
- `src/solvers/algebraic/groebner.cpp` — `compute()` and
  `extract_candidate()`.
- `bench-multiplication/saber/make-saber-query.py` — current
  per-coefficient workaround consumer.
