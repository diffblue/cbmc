# Paper 2 Future Directions: Status and Sequencing (2026-05-27)

This document consolidates the future-direction state for the
algebraic procedure as of 2026-05-27. It supersedes the ad-hoc
"Re N" label scheme used across earlier per-experiment notes.

## Status table

| Label | Direction | Status | Notes |
|---|---|---|---|
| Re 1 | Disjunctive-disequalities procedure-level extension | **IMPLEMENTED** | Commit `448bb10923`. See `disjunctive-disequalities-extension.md`. |
| Re 2 | Extractor coverage extensions ("C-narrow") | **FOLDED INTO Re 4** | bvshl with constant `k` already handled. bvlshr / exact division / bvand / bvor / bvxor cannot be extracted soundly without bit-decomposition. See "Why C-narrow is folded" below. |
| Re 3 | Expression-level normalisation via Gröbner basis | Sanity-passed | `ENABLE_GB_EXPR_NORMALISE` prototype exists in CBMC. Lower priority than Re 4. See `expression-normalisation-design.md`. |
| Re 4 | Bit-decomposition variables | **NEXT PUSH** | Sanity check passed (8-bit commutativity + 8 idempotency + 2 sum-decomposition still solves in 0.00s). Estimated 4–8 weeks for production. Subsumes Re 2 and unlocks the universal-relational and existential-relational classes. See `saber-experiment-2026-05-26.md` and "Re 4 scope and sub-goals" below. |
| Re 5 | (reserved) | — | |
| Re 6 | SABER Level A empirical study | **DONE** | Commits `b7057820c5`, `7fabd71ffc`, `5419a39767`, `5a5960d93a`, `624237a09b`, `37c5c7d781`, `a07f659cf5`. §4.3 of paper.tex. |
| Re 7 | ZFP injection into Gröbner basis | Negative result | See `zfp-injection-result.md`. |
| Re 8 | Theory combination (refactor bit-vector pipeline into theory-solver-style module) | Long-term | 2–4 months architectural work. Not in scope for the TACAS 2027 deadline. |

## Why C-narrow is folded into Re 4

C-narrow was originally scoped (2026-05-26) as a targeted set of
extractor extensions for `bvshl k` (constant), `bvlshr k`
(constant, exact division), and possibly `bvconcat` / bitwise
operators. The intent was to unlock Toom-Cook 4-way SABER
verification (faithful to the actual SABER algorithm) and the
GRS-128 community benchmark.

Investigation on 2026-05-27 (commits `e79a8fbca5` and the
revert `a085c50177`) established that `bvlshr` cannot be
soundly extracted as a polynomial operation, even with a
flag-gated assumption of divisibility. The fundamental obstacle
is that `bvlshr` is not a polynomial operation in
$\mathbb{Z}_{2^d}$: take $d = 4$ and $c = 9$. Then
$2c \bmod 16 = 2$, so $(2c) \gg 1 = 1$, but the polynomial form
"$c$" with $c = 9$ yields $9$. Modular reduction has happened
by the time we see the polynomial; pattern-matching divisibility
on coefficients cannot recover the lost bits. Similar arguments
apply to `bvand`, `bvor`, `bvxor`, etc. — they are partial
operations on the bit-level representation of values, not
polynomial operations on the values themselves.

The sound encoding requires bit variables. With
$b_{a,i} \in \{0, 1\}$ (idempotency $b_{a,i}^2 = b_{a,i}$) and
sum-decomposition $a = \sum_i 2^i b_{a,i}$:

- $a \gg k = \sum_{i = k}^{d-1} 2^{i-k} b_{a,i}$.
- $\mathit{bvand}(a, b) = \sum_i 2^i (b_{a,i} \cdot b_{b,i})$.
- $\mathit{bvor}(a, b) = \sum_i 2^i (b_{a,i} + b_{b,i} - b_{a,i} \cdot b_{b,i})$.
- $\mathit{bvxor}(a, b) = \sum_i 2^i (b_{a,i} + b_{b,i} - 2 b_{a,i} \cdot b_{b,i})$.

Each is a sound polynomial expression in the bit variables.

Hence: C-narrow is not a separate direction; it is a
straightforward consequence of Re 4 once the bit-decomposition
machinery is in place. Folding the two avoids shipping
half-complete and unsound bvlshr support behind a flag.

## Re 4 scope and sub-goals

**Goal.** Make the algebraic procedure sound on a class of
queries containing partial bit-vector operations (`bvlshr`,
`bvand`, `bvor`, `bvxor`, plus relational predicates
`bvult`/`bvslt`).

**Sub-goals.**

1. **On-demand bit-decomposition.** When the extractor encounters
   a partial-bit-vector operator on a polynomial-extractable
   sub-expression, expand the relevant operand's bit
   representation: introduce $d$ bit variables, add idempotency
   constraints ($b_{a,i}^2 = b_{a,i}$ for each $i$), and add the
   sum-decomposition constraint
   ($a - \sum_i 2^i b_{a,i} = 0$). Cache per-variable so each
   polynomial variable is decomposed at most once.

2. **Polynomial encoding of partial operators.** Replace
   `bvlshr a k` with $\sum_{i = k}^{d-1} 2^{i-k} b_{a,i}$, etc.
   (formulas above).

3. **Buchberger tractability at scale.** Sanity check passed
   at $d = 4$ for one variable (8 bit constraints total). Real
   queries will introduce $d$ bit constraints per partial-
   operator argument; for $d = 16$ with 4 partial-operator
   arguments, that's 64 idempotency + 4 sum-decomposition
   constraints. Empirical question: does Buchberger remain
   tractable? The 2026-05-26 sanity check suggests yes at small
   $d$, but the answer for $d = 16$ and SABER-scale systems
   needs measurement before we commit.

4. **Faithful Toom-Cook 4-way SABER.** Application: write a
   `--algo-b toom4` mode for `make-saber-query.py` that uses
   the actual SABER interpolation formulas (with `>> 1`,
   `>> 3`, modular inverses). Verify against schoolbook with
   Re 4-enabled procedure. Adds a column to §4.3's
   `tab:saber-scaling`.

5. **GRS-128 community benchmark.** If locatable in SMT-LIB,
   test whether Re 4 unlocks it and add to §4.5's table.

6. **Universal-relational class.** Extends the procedure beyond
   universal-equational. Queries like
   $\forall a, b \in \mathbb{Z}_{2^d}.\ (a < b) \implies (a + 1 \leq b)$
   become decidable. This is a *class-coverage* extension, not
   just a syntactic-coverage extension.

**Estimated effort.** 4–8 weeks for a working prototype that
integrates sub-goals 1–3. Sub-goals 4–5 follow from sub-goal 1
and are 1–2 days of generator work each. Sub-goal 6 is a class
of queries we can write into the evaluation once the
infrastructure is in place.

## Sequencing

1. **Now (2026-05-27 → 2026-06-02)**: holding pattern while
   Paper 1 peer review feedback arrives. No major Paper 2
   changes.
2. **2026-06-02 → 2026-06-15**: Re 4 design doc — write a
   detailed implementation plan for sub-goal 1
   (on-demand bit-decomposition entry point in
   `boolbv.cpp::try_algebraic_solve`). Includes the empirical
   tractability check at $d = 16$.
3. **2026-06-15 → 2026-08-01**: Re 4 implementation. Land
   sub-goals 1–3.
4. **2026-08-01 → 2026-08-31**: Re 4 application — sub-goals
   4–6. Update §4.3 of paper.tex with faithful Toom-4 SABER if
   it works.
5. **2026-09-01 → 2026-10-01**: Paper 2 final pass. TACAS 2027
   deadline 2026-10-15.

## Cross-references

- `saber-experiment-2026-05-26.md` — SABER Level A empirical
  study + Re 4 sanity check + the fold of C-narrow into Re 4.
- `disjunctive-disequalities-extension.md` — Re 1 implementation
  notes.
- `expression-normalisation-design.md` — Re 3 prototype design.
- `bit-level-polynomial-design.md` — earlier (2026-05-16) notes
  on bit-level encoding; partly subsumed by this doc.
- `martin-notes-2-analysis.md` — earlier (2026-05-16) notes on
  research directions; uses a different numbering scheme.
- `paper.tex` §4.3 (SABER) and §4.5 (SMT-COMP sample) — current
  Paper 2 sections affected by Re 4.
