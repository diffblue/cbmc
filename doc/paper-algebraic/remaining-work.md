# Algebraic Pre-Solver — Remaining Work and Open Items

This document lists work that is incomplete or unexplored after
Plan A.1 / A.2 / A.3 (commit b0aaed56bd on branch
`features/adder`). Items are tagged with priority, effort,
expected impact, and any dependency on prior work.

The current state (post Plan A.3 + F4 + Items 2/4/5/6/9):
- **41/66 SMT-COMP** stratified sample (was 36/66 baseline; +5
  unlocks total: cohencu_0..3, geo3.c_5).
- **133/210 Brain's random-polynomial sample** (was 128 in
  paper; +5 vs paper, +14 vs `martin-subpoly-comparison-v2.tsv`).
- div/mod identity at every bit-width tested (8 → 256) now
  solves in <1.4 s (Plan A.3); also `b != ~0` form (Item 2
  extension).
- F4-style tail reduction (Item 8) closes cohencu_2/3 (Item 1).
- Synthetic high-half-extract regression fixed (Item 6): 4.0 s
  → 0.020 s on 64-bit overflow check.
- 4 wins-beyond-all-current-solvers in Brain's 210 sample,
  $10\times$ faster than prior measurement.
- 65 Lean traceability entries across 20 modules, all status
  **DONE** (zero `sorry`, zero project-specific axioms; only
  standard mathlib axioms `propext`, `Classical.choice`,
  `Quot.sound`). Item 9 closed `DONE-MOD-AXIOMS` for `Defer.lean`.
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

### Item 6 — Synthetic regression cleanup — **COMPLETED**

**Status**: **Done** (commit on `features/adder`).

**Effort spent**: half a day.

**Fix**: detect non-zero-LO extractbits in disequality LHS or
RHS at the time we collect from `set_to`, and skip pushing to
`algebraic_disequalities`. The disequality remains visible to
`SUB::set_to` for bit-blasting; only the algebraic processing
is skipped. The guard applies ONLY to disequalities, not to
equalities, because the Tseitin propagator (Phase 2.6) uses
extractbits-on-boolean-atom equalities for forward and backward
chain propagation; an earlier draft that guarded equalities
caused `wienand_Booth_mult_ub_8x8_1.sf` to regress.

**Result**: synthetic 64-bit overflow check 4.0 s → 0.020 s
(200×). 41/66 SMT-COMP preserved. 0 regressions. New regression
test: `regression/smt2_solver/highhalf-extract-skip/`.

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

### Item 9 — Lean tightening (`DONE-MOD-AXIOMS` → `DONE`) — **COMPLETED**

**Status**: **Done** (commit on `features/adder`).

**Effort spent**: half a day.

**Result**: The three theorems in `Defer.lean`
(`defer_replay_equivalence`, `defer_verdict_equivalence`,
`defer_verdict_from_empty`) were marked `DONE-MOD-AXIOMS` in
`TRACEABILITY.md`, but a previous revision of `Defer.lean` had
already replaced the two semantic axioms
(`defer_finish_eq_eager_finish`, `finish_eager_commutes`) with
provable theorems under a concrete set-based abstract model of
`SolverState`. The "mod-axioms" status was stale documentation.
Verified mechanically with `#print axioms`: each of the three
theorems depends only on the standard mathlib axioms `propext`
and `Quot.sound`, no project-specific axioms.

Updates: `TRACEABILITY.md` 3 entries → DONE; status legend
simplified (only DONE category remains); `boolbv.cpp` `PROOF:`
comment rewritten to reflect that A1/A2 are now theorems.

The repository now has **zero `DONE-MOD-AXIOMS`** entries; all
65 traceability entries across 20 Lean modules are
unconditional `DONE`.

---

### Item 10 — Precise characterisation of the incompleteness fragment

**Status**: Open. (Origin: Armin's review comments, June 2026.)

**Motivation**: Our formal artefact establishes soundness and
also explicitly disproves naïve completeness
(`StrongGB.lean::naive_completeness_is_false`,
`two_trick_saturation_complete_is_false`). The current paper
acknowledges that completeness fails and explains why a full
Song et al. mechanisation is out of scope, but it does not yet
*precisely characterise* the set of UNSAT formulas that our
pipeline returns UNKNOWN on. Doing so has two payoffs:

1. **Honest scope statement** for the paper: a formal
   description of the fragment we are decisive on, and a formal
   description of the fragment we are not.
2. **Engineering guidance**: every benchmark that times out or
   returns UNKNOWN sits at one of a small number of well-defined
   gates in the pipeline. If we can name those gates precisely,
   we can review which ones are amenable to local extension —
   possibly with payoff on real benchmarks.

**Effort**: 1–2 weeks. Phase split:

**Phase 1 — characterise (Lean + prose, ~1 week)**:
The pipeline has four sequential gates that each decide whether
a formula is "in" or "out" of the algebraic fragment. Each gate
already has a soundness theorem; what we need is an explicit
*negative* characterisation:

- **Gate A — set_to filter** (`boolbv.cpp::set_to`,
  `walk_for_algebraic`). Equalities/disequalities reach the
  algebraic_(dis)equalities buckets only if neither side is an
  internal `__CPROVER` symbol and (for disequalities since
  Item 6) neither side contains a non-zero-LO extractbits.
  *Out:* anything filtered here is a free variable to bit-blast.
- **Gate B — poly_extract** (`poly_extract.cpp::to_polynomial`).
  An expression becomes a `polynomialt` only if every operator
  is in `{+, -, *, neg, concat-with-zero, low-bit-extract,
  shift-by-constant-with-zero-fill, …}`. *Out:* anything
  containing `bvudiv`/`bvurem` outside the Phase A.3 fast-path,
  high-LO `extract`, variable-amount shifts, bvashr,
  bvxor/bvand/bvor (we have these only inside `decompose_bits`).
- **Gate C — strongGB ideal-membership of an odd constant**
  (`groebner.cpp::compute`). Even if every disequality is
  polynomialised cleanly, refutation only succeeds when the
  augmented ideal contains an odd constant. The two
  `*_completeness_is_false` theorems give explicit
  counterexample shapes (e.g.\ `{C 2}` over `ZMod (2^d)` with
  `d > 1`). *Out:* polynomial systems whose ideal is a strict
  ideal of `ZMod (2^d)` (no odd unit reachable). The Song et al.
  encoding identifies a sub-class where this gate is complete.
- **Gate D — Buchberger termination/budget**. Even when all of
  A/B/C are favourable in principle, the pair queue may not
  terminate within the budget. The pair-selection theorem
  (`pair_selection_orthogonal`) and the F4 tail-reduction
  theorem (`tail_reduction_in_ideal`) constrain *what* the
  procedure can derive but not *when*.

For each gate we want a Lean theorem of the form
"if formula $\varphi$ has property $P_\text{gate}(\varphi)$ then
the gate emits UNKNOWN regardless of subsequent gates".
Together these compose into a precise predicate
$\text{InFragment}(\varphi)$ such that
$\text{InFragment}(\varphi) \land \varphi \text{ unsat}
\Rightarrow$ pipeline returns UNSAT.

**Phase 2 — review and shrink (engineering, ~1 week)**:
Once the predicate is in hand, take the SMT-COMP unsolved 25/66
and Brain's 77/210 unsolved benchmarks and classify each:

| Bucket | Example                              | Failing gate    |
|--------|--------------------------------------|-----------------|
| B-shift | log-slicing_*                       | B (variable shifts) |
| B-divmod | hand-crafted div checks            | B (bvudiv outside FP) |
| B-extract | brummayerbiere2_*ulov*             | B (high-LO extracts) |
| C-witnessable | most multiplier overflows      | C (no odd constant) |
| D-budget | bw=512 case 4                      | D (timeout)     |

For each bucket, the question is: can we extend the gate locally
*without compromising soundness*? Concrete candidates the
analysis would produce:

- *Constant-amount* `bvshl/bvlshr` admits a polynomial
  representation $x \cdot 2^k$ resp.\ $\lfloor x / 2^k \rfloor$;
  the latter introduces a fresh quotient variable but the
  resulting system is still in our fragment. Lifting this in
  Gate B might unlock log-slicing.
- *High-LO* `extract` $((\_~\text{extract}~\text{hi}~\text{lo}))$
  with $\text{lo} = k \cdot w$ and the source being a
  `concat`-of-zext is bit-trivial; the corresponding polynomial
  is $x \mod 2^{\text{hi}+1}$, already in our fragment. Lifting
  this in Gate B might unlock the synthetic high-half pattern
  (already partly handled by Item 6, but only as an early-out;
  this would let the algebraic side actually use the
  expression).
- The Konrad/Scholl FMSD 2026 *phase optimisation* technique
  (negative-Davio normalisation of intermediate polynomials)
  attacks Gate D directly: it keeps Buchberger basis sizes
  small on circuits with large OR-trees. Adapting it to our
  ZMod fragment is non-trivial (their setting is $\mathbb{Z}$
  with `x^2 = x`) but plausibly addresses the bw=512 timeouts.
- *Forward information propagation* à la Scholl and Konrad
  (DAC 2020) fits Gate C: it adds polynomials derivable from
  input constraints (e.g.\ `0 ≤ R(0) < D · 2^{n-1}`) to the
  basis. In our setting the analogous information is what
  Tseitin propagation already extracts; making this precise
  would clarify the relationship.

**Expected concrete impact**:
- Paper-side: a "fragment characterisation" paragraph or
  subsection in `sec:future-within-and-beyond` with the four
  gates, the corresponding Lean predicates, and an explicit
  classification of unsolved benchmarks. This is the kind of
  *honest scope* that reviewers reward.
- Engineering-side: 1–2 new gate-extensions, each defended by
  a Lean theorem, each potentially worth a handful of unlocks.
  Specifically, lifting Gate B for constant-amount shifts is
  cheap (a few hours of code + a 1-page Lean proof) and the
  most likely to pay off.

**Cross-references**: existing artefacts to compose:

- `StrongGB.lean::naive_completeness_is_false` — already
  characterises Gate C negatively (with `{C 2}` counterexample).
- `StrongGB.lean::d_eq_one_completeness` — Gate C is positively
  complete at `d = 1`; this is one example of a sub-fragment.
- `StrongGB.lean::WellFormedEncoding` — placeholder predicate
  for the Song et al. fragment; could be the basis of a richer
  Gate-C predicate.
- `Re4.lean::all_idempotent_to_bool` — already shows that
  idempotency suffices to make variables Boolean.
- `BvDivPolyEncoding.lean` — already characterises when
  `bvudiv`/`bvurem` are polynomialisable; this is the positive
  side of Gate B for div/mod.

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

---

## Reviewer feedback — Armin Biere (June 2026)

Pointers passed by Armin via `~/armin-comments.txt`. Captured
here so the related-work and benchmark threads can be picked up
later.

### Konrad–Scholl SCA line at FMCAD/FMSD

**Reviewed papers** (all in `~/`):

- `alexander_konrad_fmsd.pdf` — Konrad & Scholl, FMSD 2026,
  *"Symbolic computer algebra for multipliers revisited —
  demonstrating the significance of order and phase
  optimization"*. Extended journal version of their FMCAD 2024
  paper. Key technique: backward-rewriting with **dynamic phase
  optimisation** (greedy negation of newly-introduced variables
  to keep intermediate-polynomial size small) and **dynamic
  order optimisation** at the EAB (extended-atomic-block)
  hierarchy level. Tool: DynPhaseOrderOpt. Solves 801/930
  64-bit multiplier benchmarks across optimisation variants
  (vs. 273 for AMulet 2.2, 234 for TeluMA, 620 for RevSCA-2.0,
  601 for DyPoSub). Industrial Synopsys multipliers: solves up
  to $256\times256$ (2's complement, ${\sim}700$k AIG nodes).
  Generates LPAC-format certificates. **Coefficient ring is
  $\mathbb{Z}$ with $v^2 \to v$ reductions**, not our
  $\mathbb{Z}_{2^d}$.

- `KSM_2024.pdf` — Konrad, Scholl, Mahzoon, Große, Drechsler,
  FMSD 2024, *"Divider verification using symbolic computer
  algebra and delayed don't care optimization"*. Extended
  journal version of their FMCAD 2022. Key technique:
  satisfiability-don't-care optimisation on EABs +
  delayed-don't-care-optimisation (DDCO) — instead of
  immediately optimising a polynomial when its
  don't-care-input variables appear, accumulate don't-cares and
  optimise only when needed. Solves dividers up to 512-bit.
  **Forward information propagation** of input constraints
  (e.g.\ $0 \le R^{(0)} < D \cdot 2^{n-1}$) is essential for
  divider verification: without it, intermediate polynomials
  blow up exponentially (formally proven in Sect. 4 of the
  paper). This is closely analogous to our Tseitin propagation
  step.

- `konrad_fmcad2025.pdf` — proceedings volume; the relevant
  paper inside is Konrad & Scholl FMCAD 2025, *"FastPoly: An
  Efficient Polynomial Package for the Verification of Integer
  Arithmetic Circuits"*. C++ polynomial package using
  `std::set<Monom>` plus a per-variable `refList` of doubly-linked
  lists for $O(1)$-per-variable substitution. Up to
  $50\times$ faster than AMulet 2.2's library on 256-bit
  multipliers. Independently useful as an engineering data
  point — our own polynomial library could adopt this
  representation if substitution becomes a bottleneck.

**Pointers we extracted from these papers**:

- *Benchmarks for stress-testing*: aoki [17], GenMul [38, 41]
  and multgen [49] generators, Synopsys-generated industrial
  multipliers (4 → 256-bit). Konrad & Scholl publish binaries
  and benchmark sets at
  `https://abs.informatik.uni-freiburg.de/src/projects_view.php?projectID=24`.
  All these are gate-level AIG benchmarks; our SMT-LIB
  evaluation cannot use them directly, but if we ever pursue
  Item 7 (gate-level + algebraic hybrid) they are the natural
  baseline.
- *Phase optimisation* — directly relevant to our Item 10
  Phase 2 review. Their setting differs (ours is
  $\mathbb{Z}_{2^d}$ rather than $\mathbb{Z}$ with field
  polynomials) but the technique is general: greedy
  negate-and-test to shrink intermediate polynomials.

**Other Konrad papers we have NOT yet read** (would request
copies if relevant work proceeds):

- Scholl & Konrad, DAC 2020, *"Symbolic computer algebra and
  SAT-based information forwarding for fully automatic divider
  verification"* — the SBIF foundational paper. The KSM 2024
  journal extension [27] cites it heavily; we have the
  derivative content but not the original.
- Scholl, Konrad, Mahzoon, Große, Drechsler, DATE 2021,
  *"Verifying dividers using symbolic computer algebra and
  don't care optimization"* — predecessor of KSM 2024 [28].
  Same content, but might have additional design discussion.
- Mahzoon, Große, Scholl, Konrad, Drechsler, DAC 2022,
  *"Formal verification of modular multipliers using symbolic
  computer algebra and Boolean satisfiability"* — modular
  multipliers are closer to our setting (residue arithmetic)
  than the standard integer multipliers, so this is the most
  promising of the unread items for our line of work.

### Roole / Roolean (Onderka, Biere, Fleury, FMCAD 2026 submission)

`fmcad26-submission.pdf` — Onderka, Biere, Fleury, *"Lean
Certified Bitvector Solving without Bitblasting"*.

**One-paragraph summary**: an alternative paradigm to
bv\_decide for certified QF\_BV. They build a pair of solver
twins: an untrusted Rust solver (Roole) and a trusted Lean
proof-checker (Roolean), both using the same simplified TVAR
(three-valued abstraction refinement) procedure. The proof
certificate is a *splitting tree* — a decision tree where each
non-leaf node splits one bit to 0 and 1 — produced by Roole and
consumed by Roolean as an oracle. Roole + Roolean produces
trusted UNSAT verdicts for 17 433 / 27 758 (62.8%) of the 2024
QF\_BV unsat benchmarks within 1200 s + 8 GB; total certificate
size is 1.64 GB, mostly $<$1 kB per certificate. Comparison: bv\_decide
solves slightly more but with order-of-magnitude larger
certificates and significantly more memory.

**Position relative to our work**: Roole/Roolean is a *direct
competitor to bv\_decide*, the tool that our paper currently
positions itself against. They occupy the same
"trusted / certified QF\_BV" space we do, but via a completely
different mechanism (ternary abstraction + DPLL-style splitting
tree, no bit-blasting at all). Our paper should at minimum cite
them and discuss the contrast:

- *Coverage*: theirs is general QF\_BV (same scope as bv\_decide,
  Bitwuzla); ours is restricted to multiplication-heavy
  arithmetic identities.
- *Mechanism*: theirs is purely SAT/abstraction-based; ours is
  algebraic.
- *Trust story*: theirs uses the twin-solver oracle pattern,
  small certificates, full Lean formalisation including the
  evaluator semantics. Ours uses SCA traceability comments and
  Lean theorems for the algorithmic core; we do *not* generate
  per-query certificates (the Lean theorems witness the
  algorithm rather than each run).

The twinning idea is interesting in its own right and could
inform a follow-on direction: rather than mechanising the
algorithm-level soundness of strong-GB once (as we do), one
could imagine a per-query LPAC-style certificate emitted by our
solver and replayed by a Lean twin. Konrad–Scholl FMSD 2026
already does this with PACHECK 2.0 as the external checker;
porting the checker to Lean would be analogous to Roolean.

**Action items from this review**:

1. Add a short related-work paragraph to the paper covering
   Roole/Roolean and Konrad/Scholl. Position our contribution
   precisely: we are **not** a general QF\_BV solver and we are
   **not** a multiplier-circuit verifier; we are an algebraic
   pre-solver for SMT-LIB queries with multiplication.
2. The "splitting tree as proof certificate" idea is a useful
   prompt for Item 7: a CBMC pipeline that emits a small witness
   tree (which assertions reduced to which polynomial residues)
   would ride the same Lean-checker pattern.
3. The Konrad/Scholl phase-optimisation technique should be
   evaluated as a candidate Phase-2 extension under Item 10
   (Gate D shrinking).
