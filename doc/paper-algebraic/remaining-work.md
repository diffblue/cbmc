# Algebraic Pre-Solver — Remaining Work and Open Items

This document lists work that is incomplete or unexplored after
Plan A.1 / A.2 / A.3 (commit b0aaed56bd on branch
`features/adder`). Items are tagged with priority, effort,
expected impact, and any dependency on prior work.

The current state (post Plan A.3 + F4 + Items 2/4/5):
- **41/66 SMT-COMP** stratified sample (was 36/66 baseline; +5
  unlocks total: cohencu_0..3, geo3.c_5).
- **133/210 Brain's random-polynomial sample** (was 128 in
  paper; +5 vs paper, +14 vs `martin-subpoly-comparison-v2.tsv`).
- div/mod identity at every bit-width tested (8 → 256) now
  solves in <1.4 s (Plan A.3); also `b != ~0` form (Item 2
  extension).
- F4-style tail reduction (Item 8) closes cohencu_2/3 (Item 1).
- 4 wins-beyond-all-current-solvers in Brain's 210 sample,
  $10\times$ faster than prior measurement.
- 144+ Lean theorems across 20 modules; zero `sorry`s in
  project code; standard mathlib axioms only.
- bw=512 family (4/5), Wienand commute*/distrib* (4/4),
  SABER (3/3) preserved.
- Paper updated: SMT-COMP, Brain's 210, SABER, custom-suite
  tables; new sections on Phase A.3, F4, Plan B negative
  finding.

**Status legend**:
- **Open**: not yet started.
- **Documented**: investigation complete, design captured, no
  implementation.
- **In progress**: actively being worked on.
- **Deferred**: deliberately deprioritised (with rationale).

---

## Concrete capability gaps

### Item 1 — Cohencu_2/3 unlock — **COMPLETED via Item 8**

**Status**: **Done** (commit on `features/adder` after `b0aaed56bd`).
The cohencu_2/3 gap turned out to be the SAME gap as Item 8 (F4
tail reduction): the missing capability was tail-term reduction
when the basis polynomial's leading monomial sorts after the
target term in grevlex. Implementing F4-style `interreduce_basis`
(Item 8) unlocks both cohencu_2 (T/O → 3.5 s) and cohencu_3
(T/O → 1.8 s).

**Effort spent**: 1 day (well under estimate).

**Result**: +2 SMT-COMP unlocks; 39/66 → 41/66 with zero
regressions.

---

### Item 2 — Plan A.3 extension to other predicates — **COMPLETED**

**Status**: **Done** (commit on `features/adder` after F4 commit).
Extended Plan A.3's `nonzero_fast_path` to also recognise
`x != ~0` patterns. Refactored the pattern-detection logic into a
single helper applied uniformly to direct-relational and
not-relational set_to paths (the latter is essential because the
parser rewrites `bvult x ~0` to `not (x >= ~0)`).

**Effort spent**: half a day.

**Result**: 0 new SMT-COMP unlocks (no benchmark in our sample
exercises the `x != ~0` form alongside `bvudiv`/`bvurem`), but
synthetic div/mod identity with `b != ~0` now solves at all
bitwidths (was T/O at 16+ before). Regression test added.

**Note on synthetic high-half regression**: the 4× slowdown on
the `(extract 2N-1 N) (bvmul ...)` pattern noted in
`plan-B-empirical-findings.md` was NOT addressed by this
extension; it requires a different fix (skip algebraic
processing for disequalities involving non-zero-LO extractbits).

---

### Item 3 — Constraint-system scalability for VS3 / Sage2

**Status**: Open. Diagnosed: 100+ algebraic equalities cause
the per-disequality Buchberger to repeatedly process a giant
basis, choking on benchmarks like VS3_A11 (518 asserts) and
VS3_S1 (336 asserts).

**Effort**: ~1 week.

**Targeted improvements**:
- **SSA chain compression**: pre-process algebraic_equalities to
  substitute non-recursive definitions before Buchberger sees
  them (currently only partial substitution happens).
- **Polynomial deduplication**: identical or trivially-related
  polynomials get added multiple times after extraction.
- **Per-disequality basis pruning**: skip equalities whose
  support doesn't overlap with the disequality's support.

**Expected impact**: +2–3 SMT-COMP unlocks (VS3_A11, VS3_S1,
possibly Sage2_bench_9381).

---

## Engineering / methodology

### Item 4 — Fresh paper evaluation — **COMPLETED**

**Status**: **Done** (commit on `features/adder`). Re-ran all
benchmark suites with the post-F4 binary; updated paper tables.

**Effort spent**: 1 day.

**Results**:
- Brain's 210: 119 → **133** (`all_combined`; +14 unlocks vs
  prior `martin-subpoly-comparison-v2.tsv`; 0 regressions).
- Custom suite: 39/39 (preserved).
- DSP: 5/5 in <0.015 s each (preserved).
- SABER scaling: every measured N modestly faster
  (e.g.\ N=256 from 14.27 s → 11.25 s).
- 4 wins-beyond-all-current-solvers preserved with $10\times$
  faster average runtime.

---

### Item 5 — Update paper with Plan A.3 + div/mod identity — **COMPLETED**

**Status**: **Done** (commit `fc56bdd9bf` on `features/adder`).

**Effort spent**: half a day.

**Additions made**:
- Phase A.3 narrative paragraph (relational predicate fast-path).
- div/mod identity benchmark (table at every bit-width).
- F4 paragraph: tail reduction; cohencu_2/3 unlock.
- 'Hybrid Z/ZMod overflow reasoning is not enough on its own'
  paragraph in `sec:future-within-and-beyond` (Plan B negative
  finding).
- New citation: `faugere1999f4`.

---

### Item 6 — Synthetic regression cleanup

**Status**: Documented. The high-half-extract pattern
`(extract 2N-1 N) (bvmul (zext s) (zext t))` with a bvule
bound is 200× slower in default than bit-blast-only on
synthetic benchmarks.

**Effort**: ~1–2 days.

**Engineering polish**:
- Detect the pattern in `set_to`.
- Skip the algebraic processing for these disequalities (they
  don't fit our fragment).
- Let bit-blasting handle them directly.

**Expected impact**: 0 SMT-COMP unlocks (pattern not in our
sample), but cleaner pipeline behaviour.

---

## Scientific frontiers

### Item 7 — Gate-level + algebraic hybrid

**Status**: Documented frontier. The ~16 SMT-COMP benchmarks
(brummayerbiere2_*ulov*, log-slicing_*, galois_*, calypto,
BuchwaldFried, isqrtadd, Booth_mult) require AIG-aware
polynomial reasoning of the kind in Biere-Kauers-Ritirc 2017
and Kaufmann-Biere 2021.

**Effort**: Multi-month follow-on paper.

**Research directions**:
- **Topological gate ordering**: extract polynomial relations
  from CBMC's bit-level SSA in reverse topological order
  (mimicking AIG-aware Gröbner solvers).
- **Hybrid procedure**: when high-half-extract patterns are
  detected AND a corresponding bit-level circuit exists,
  dispatch to a specialised gate-level solver instead of
  bit-blasting.
- **AIG-multiplier equivalence**: the Amulet2 problem space.

**Status quo**: paper's `sec:gate-level` acknowledges this gap
but has no concrete approach.

---

### Item 8 — F4-style matrix reduction — **COMPLETED**

**Status**: **Done** (commit on `features/adder`). The smallest
functionally meaningful F4-style step was implemented: tail
reduction (`full_reduce`) and basis interreduction
(`interreduce_basis`) wired into an outer
"Buchberger → interreduce → regenerate pairs → Buchberger"
loop in `compute()`.

This is not the full F4 (which batches multiple S-poly
reductions into a single matrix), but it captures F4's core
benefit for our use case: the ability to reduce non-leading
terms of basis polynomials, which standard incremental
Buchberger misses.

**Effort spent**: 1 day (well under the 2-3 week estimate; the
saving is because we did not implement the matrix kernel —
tail reduction without batching was sufficient for the gap we
identified).

**Concrete result**: +2 SMT-COMP unlocks (cohencu_2, cohencu_3).
Closes Item 1 in this list.

**Future extensions** (if scaling needs warrant):
- Batch S-poly reduction into a sparse matrix.
- Implement matrix row reduction with the 2-trick for ZMod(2^d)
  pivots.
- Selection of which pairs to batch (typically: all pairs with
  the smallest LCM degree in the queue).

---

### Item 9 — Lean tightening (`DONE-MOD-AXIOMS` → `DONE`)

**Status**: Open. Several Lean theorems are currently
`DONE-MOD-AXIOMS`:

- `Defer.lean::defer_replay_equivalence` (relies on
  `defer_finish_eq_eager_finish`, `finish_eager_commutes`
  axioms).
- `Defer.lean::defer_verdict_equivalence` (same chain).
- `boolbv.cpp::try_algebraic_solve` verdict soundness (relies
  on operational-semantics axioms).

**Effort**: ~1 week.

**Approach**: mechanise the operational semantics of the
boolbv layer or the strong-GB algorithm to a degree that lets
the axioms be discharged.

**Expected impact**: increases trust in the implementation;
no SMT-COMP unlock.

---

## Recommended sequencing

If chasing **incremental concrete payoffs**:
- Items 4 (paper eval), 5 (paper update), 2 (predicate
  fast-path extension). Total: 1–2 weeks.

If chasing **bigger scientific impact** in the current paper:
- Item 8 (F4 reduction). 2–3 weeks but likely unlocks
  cohencu_2/3 and gives a clean scaling story.

If chasing **a follow-on research direction**:
- Item 7 (gate-level + algebraic hybrid). Multi-month
  research project.

The current state (Plan A.1+A.2+A.3) is a defensible paper
artifact on its own. Items 4–5 alone would let us submit; the
rest are improvements rather than necessities.

---

## Cross-references

- Plan A design: `doc/paper-algebraic/plan-A-buchberger-tuning.md`
- Plan B design (deferred): `doc/paper-algebraic/plan-B-hybrid-z-zmod.md`
- Plan B empirical findings:
  `doc/paper-algebraic/plan-B-empirical-findings.md`
- Plan A/B synthesis:
  `doc/paper-algebraic/plans-AB-synthesis.md`
- Paper section on tuning: `paper.tex::sec:algebraic-tuning`
- Lean traceability: `formal-proofs/TRACEABILITY.md`
