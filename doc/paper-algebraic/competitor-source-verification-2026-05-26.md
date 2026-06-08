# Bitwuzla and cvc5: Source-Code Verification of Algebraic Reasoning Claims

*Date: 2026-05-26*
*Purpose: verify the (G) headline claim that Bitwuzla and cvc5
"dispatch arithmetic identities heuristically" before committing
the claim to Paper 2's abstract.*

Sources inspected:
- `~/bitwuzla.git` (Bitwuzla 0.9.0-dev-main@72ecd081)
- `~/cvc5.git` (cvc5 1.3.3, branch HEAD)

## Bitwuzla

### What is present

**Pattern-based rewrites:**
- `src/rewrite/rewrites_bv.cpp` (4261 lines) — main BV rewrite rules.
- `src/rewrite/rewrites_bv_norm.cpp` (425 lines) — normalisation
  rules: `NORM_BV_ADD_MUL`, `NORM_BV_CONCAT_BV_NOT`,
  `NORM_BV_NOT_OR_SHL`, `NORM_BV_SHL_NEG`,
  `NORM_BV_EXTRACT_ADD_MUL_REV1/2/3`, `NORM_BV_MUL_POW2_REV`,
  `NORM_FACT_BV_ADD_MUL`, `NORM_FACT_BV_ADD_SHL`,
  `NORM_FACT_BV_SHL_MUL`, `NORM_FACT_BV_MUL_SHL`.

**Occurrence-map canonicalisation:**
`src/preprocess/pass/normalize.cpp` (`PassNormalize`). The pass
builds an `OccMap` (term-to-count map) for each side of an
equality, applies `compute_occurrences_add` /
`compute_occurrences_mul`, then equates by "factor out common
subterms". Key methods:
- `normalize_mul(node, OccMap&, bool keep_value)`
- `normalize_add(node, OccMap&, bool, bool)`
- `normalize_comm_assoc(parent_kind, node0, node1)` — the
  commutative/associative normaliser; handles only
  `BV_ADD` and `BV_MUL`.

**Solving back-ends** in `src/solver/bv/`:
- `bv_bitblast_solver.cpp` (AIG bit-blasting + SAT solver)
- `bv_prop_solver.cpp` (propagation-based local search)

### What is absent

`grep -rli 'gr.bner\|groebner\|polynom.*ideal\|polynomial.*ring\|buchberger' src/ include/`
→ **0 hits.**

There is no Gröbner basis, polynomial-ideal, or any related
algebraic decision procedure anywhere in Bitwuzla.

### Conclusion (Bitwuzla)

Bitwuzla's arithmetic-identity handling is:
1. Pattern rewrites (`rewrites_bv*.cpp`).
2. Occurrence-map canonicalisation (`PassNormalize`),
   complete for commutativity and associativity.
3. Bit-blasting fallback when 1+2 do not close the goal.

**Bitwuzla is complete for commutativity and associativity of
$+$ and $\cdot$ via the OccMap canonicalisation, but is incomplete
for richer polynomial identities (e.g.\ $(a+b)^3 = a^3 + 3a^2b
+ 3ab^2 + b^3$ where the RHS would need full expansion before
OccMaps match), and incomplete for vanishing polynomials (e.g.\
$4x^2 + 4x \equiv 0 \pmod 8$ where the coefficient relations
matter).**

## cvc5

### What is present in QF\_BV

**Pattern-based rewrites:**
- `src/theory/bv/rewrites/`,
  `src/theory/bv/rewrites-elimination/`,
  `src/theory/bv/rewrites-simplification/` —
  three categorised directories of BV rewrite rules.

**Bit-blasting solver:**
- `src/theory/bv/bv_solver_bitblast.cpp`,
  `src/theory/bv/bv_solver_bitblast_internal.cpp`. The header
  comment of `bv_solver.h`: "Bit-vector solver interface.
  Describes the interface for the internal bit-vector solver of
  TheoryBV." Only bit-blasting strategies are implemented.

**Linear Gaussian elimination over $\mathbb{Z}_{2^d}$:**
- `src/preprocessing/passes/bv_gauss.cpp`. Header comment:
  "Gaussian Elimination preprocessing pass. Simplify a given
  equation system modulo a (prime) number via Gaussian
  Elimination if possible." The implementation note clarifies:
  "given 'prime' does not have to be prime but can be any
  arbitrary number. However, if 'prime' is indeed prime, GE is
  guaranteed to succeed, which is not the case, otherwise."
  Crucially, this pass operates on **linear equation systems**
  with **constant coefficients**: $c_1 x_1 + c_2 x_2 + \cdots
  = b \pmod{2^n}$. It does not handle nonlinear polynomial
  identities.

**QF\_BV preprocessing pipeline** (from `src/smt/process_assertions.cpp`):
```
applyPass("bv-gauss", ap);          // line 115
applyPass("normalize", ap);          // line 144
applyPass("apply-substs", ap);
…
applyPass("ext-rew-pre", ap);
applyPass("rewrite", ap);
…
applyPass("bv-intro-pow2", ap);
applyPass("bv-to-bool", ap);
applyPass("bv-to-int", ap);
…
applyPass("ackermann", ap);
…
applyPass("static-learning", ap);
applyPass("learned-rewrite", ap);
applyPass("theory-preprocess", ap);
```
None of these are Gröbner-basis-style for QF\_BV.

### What is present elsewhere (but does not apply to QF\_BV)

**Gröbner-basis reasoning in `theory/ff/`:**
- `src/theory/ff/gb.h`, `gb.cpp` — Gröbner-basis computation.
- `src/theory/ff/cocoa_encoder.cpp`, `cocoa_util.cpp` — uses
  CoCoALib for Gröbner bases.
- `src/theory/ff/Readme.md`: "The field solver implements the
  decision procedure from [OKTB23] (Ozdemir, Kremer, Tinelli,
  Barrett 2023): 'Satisfiability Modulo Finite Fields',
  essentially un-modified."

This is the **finite-field theory module**, activated by **QF\_FF
logic**, operating over **prime-order finite fields** $\mathrm{GF}(p)$.
It targets cryptographic circuit verification (e.g., zkSNARK
constraint systems).

**Logic separation** (from `src/theory/logic_info.cpp`):
`THEORY_FF` and `THEORY_BV` are separate theories. A QF\_BV query
does not activate the FF theory; the `--ff-solver` option is for
the FF theory, not BV. There is no automatic encoding of a QF\_BV
query as a QF\_FF query.

**Note on `ff_bitsum.cpp` and `ff_disjunctive_bit.cpp`:**
These preprocess passes have "ff" in their names because they
work on the FF theory (`theory/ff/parse.h`), not on BV. They are
registered in the preprocessing registry but are FF-specific.

### Conclusion (cvc5)

cvc5's QF\_BV arithmetic-identity handling is:
1. Pattern rewrites (three categorised rewrite directories).
2. `PassNormalize` — occurrence-counting canonicalisation
   similar to Bitwuzla's.
3. **Linear** Gaussian elimination modulo $2^n$ (`bv-gauss`),
   restricted to constant-coefficient linear systems.
4. Bit-blasting fallback.

cvc5 has Gröbner-basis reasoning **only for QF\_FF**
(prime-order finite fields), with no automatic encoding from
QF\_BV. **For QF\_BV with nonlinear polynomial identities over
$\mathbb{Z}_{2^d}$, cvc5 has no decision procedure; it relies on
rewriting plus bit-blasting.**

## Summary of verified facts

| Solver | Pattern rewrites | Linear modular | Gröbner over $\mathbb{Z}_{2^d}$ | Gröbner over $\mathrm{GF}(p)$ |
|---|---|---|---|---|
| Bitwuzla | yes | no | no | no |
| cvc5 (QF\_BV) | yes | yes (`bv-gauss`) | no | no |
| cvc5 (QF\_FF) | yes | n/a | n/a | yes (CoCoALib, `--ff-solver=gb`) |
| **This paper** | n/a | n/a | **yes** | n/a |

## Refinement of headline (G)

The original draft of (G) was:

> Bitwuzla and cvc5 dispatch arithmetic identities heuristically:
> when a syntactic rewrite matches, instantly; otherwise, falls
> through to bit-blasting and may time out.

This is correct in spirit but loose. A precise version:

> **Refined (G):** Bitwuzla and cvc5 dispatch arithmetic
> identities via pattern-matched rewriting and occurrence-map
> canonicalisation (complete for commutativity and associativity
> but not for richer polynomial identities); cvc5 additionally
> applies Gaussian elimination modulo $2^d$ for linear equation
> systems with constant coefficients. Neither tool implements a
> decision procedure for nonlinear polynomial identities over
> $\mathbb{Z}_{2^d}$; both fall through to bit-blasting on
> queries that do not match a rewrite pattern, and may time
> out. (cvc5's Gröbner-basis reasoning is implemented in its
> finite-field theory `theory/ff/` and applies only to QF\_FF
> queries over prime-order fields, not QF\_BV.)
>
> We give a decision procedure for the universal-equational
> fragment of QF\_BV restricted to polynomial expressions in
> $\mathbb{Z}_{2^d}$, combining a strong Gröbner basis solver
> over $\mathbb{Z}_{2^d}$ (ideal membership) and a vanishing
> polynomial test (function equivalence). The procedure decides
> 4 benchmarks at degree $\geq 13$ that defeat all current
> solvers within 10 s, all 5 DSP datapath equivalences with
> overflow cancellation in microseconds, and is bitwidth-
> independent (BW=8 to 256). Soundness is mechanised in Lean 4
> (25 theorems, 0 sorry, Mathlib contribution under review);
> the formalisation effort exposed and removed a 2000$\times$
> ordering sensitivity in the C++ implementation.

The bracketed parenthetical about cvc5's `theory/ff/` is what
distinguishes this from a casual claim. We need to keep that
distinction visible whenever we say "no algebraic procedure" —
otherwise a reviewer who knows about cvc5's `--ff` will
correctly object.

## Pre-existing claims to soft-correct

The current paper.tex says (in the related work, §9 cvc5 paragraph):

> cvc5 (\\texttt{--ff} option for QF\\_FF) integrates CoCoALib for
> Gröbner-basis reasoning over prime-order finite fields, targeting
> cryptographic circuit verification (e.g., zkSNARK constraint
> systems). Our setting is different: bit-vectors are naturally
> elements of the ring $\\mathbb{Z}_{2^d}$, which is not a field…

This is already accurate — we already distinguished QF\_FF from
QF\_BV in the related-work section. The (G) headline can lean on
this distinction; it just needs to make it visible earlier (in
§1 or even in the abstract).

## Minor: "first" claim due-diligence

The (G) draft used "first complete decision procedure". This
phrase is checkable. Care is required:
- Song et al. 2024 give the theoretical proof of completeness for
  ideal membership over $\mathbb{Z}_{2^d}$, but no SMT
  integration.
- Shekhar et al. 2007 give the vanishing-ideal characterisation
  via falling factorials; not an SMT integration.
- Gámez-Montolio et al. 2024 give the efficient normalisation
  algorithm; their target was bit-vector binary analysis, not
  SMT.
- We are the first SMT integration combining both.

Recommendation: claim "first SMT integration" or "first
implementation in a bit-vector SMT solver", not "first complete
decision procedure" (which sounds like a theoretical claim that
Song et al. would reasonably resent). The empirical claim
("decides queries that defeat all current SMT solvers") still
follows.

## Action

The (G) headline survives, with two edits:
1. Replace the "dispatch heuristically" phrase with the precise
   statement about pattern rewriting + occurrence-map
   canonicalisation + linear Gaussian elimination + bit-blasting.
2. Replace "first complete decision procedure" with "first SMT
   integration of a complete decision procedure" (or similar) to
   keep credit clear with Song et al.

Both edits make the claim stronger and more defensible, not
weaker.
