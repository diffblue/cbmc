# Paper 2 Future Directions: Status and Sequencing (2026-05-27)

This document consolidates the future-direction state for the
algebraic procedure as of 2026-05-27. It supersedes the ad-hoc
"Re N" label scheme used across earlier per-experiment notes.

*Last updated 2026-05-27 night: P1 done. DEFER_BITBLAST is now
default-on. Paper still 33 pages; new SABER scaling numbers
(headline N=256 from 109s -> 14s; N=768 newly reachable in
5.8 minutes).*

## Status table

| Label | Direction | Status | Notes |
|---|---|---|---|
| Re 1 | Disjunctive-disequalities procedure-level extension | **IMPLEMENTED** | Commit `448bb10923`. See `disjunctive-disequalities-extension.md`. |
| Re 2 | Extractor coverage extensions ("C-narrow") | **FOLDED INTO Re 4** | bvshl with constant `k` already handled. bvlshr / exact division / bvand / bvor / bvxor cannot be extracted soundly without bit-decomposition. See "Why C-narrow is folded" below. |
| Re 3 | Expression-level normalisation via Gröbner basis | Sanity-passed | `ENABLE_GB_EXPR_NORMALISE` prototype exists in CBMC. Lower priority than Re 4. See `expression-normalisation-design.md`. |
| Re 4 | Bit-decomposition variables | **MVP IMPLEMENTED + sub-goal 3 essentially complete + sub-goal 6 IMPLEMENTED + paper subsection landed** | Commits `ea3bb94f11` (design), `00d943b133` (MVP: bvlshr), `8328f31d0a` (bvand/bvor/bvxor/bvnot), `d864305fbd` (Frobenius), `61faaf0f29` (structural bit-decomp + polynomial-form host cache), `50252003e4` (inline simplification), `a54fa27f04` (linear elimination of host variables), `2049316564` (paper §4.6 + §4.3 update), `3fbc1d9c6f` (sub-goal 6: universal-relational via bvult/bvule), `889efe9588` (paper §4.6 update with sub-goal 6 results), `c9f2f825ba` (memory-efficient extraction = sub-goal 7), `49178650da` (paper §4.3 update with deferred-bit-blasting wins). Linear scaling in bitwidth on partial-bv identities. Sub-goal 6 wins on at least one Bitwuzla-T/O case (x>=2^(d-1) -> XOR/sub at bw=64). Sub-goal 7 cuts SABER memory 100-165x (now N=768 at 1.7 GB; ceiling at N=1024 is time-bound). |
| Re 5 | (reserved) | — | |
| Re 6 | SABER Level A empirical study | **DONE** | Commits `b7057820c5`, `7fabd71ffc`, `5419a39767`, `5a5960d93a`, `624237a09b`, `37c5c7d781`, `a07f659cf5`. §4.3 of paper.tex. |
| Re 7 | ZFP injection into Gröbner basis | Negative result | See `zfp-injection-result.md`. |
| Re 8 | Theory combination (refactor bit-vector pipeline into theory-solver-style module) | Long-term | 2–4 months architectural work. Not in scope for the TACAS 2027 deadline. |

## Re 4 status (post-MVP, 2026-05-27)

**Completed in this session:**

- Design doc `re4-bit-decomposition-design-2026-05-27.md`
  (architecture + sub-goal scoping + soundness argument).
- MVP implementation:
  - `decompose_bits(e)` helper in `poly_extract.{h,cpp}`.
  - `ID_lshr` extraction via bit-decomposition.
  - `ID_bitand`, `ID_bitor`, `ID_bitxor`, `ID_bitnot`
    extraction via bit-decomposition.
- All extractions are sound by construction (idempotency
  $b^2 = b$ + sum-decomposition $h = \sum_i 2^i b_i$ uniquely
  determine bits given host value).
- Synthetic tests pass: shift identities, bvand/bvor/bvxor/bvnot
  identities, the over-refute case from the previous flag-gated
  attempt now correctly answered SAT.
- Existing benchmarks unchanged (SABER scaling, Martin subpoly).

**Empirical tractability finding (after Frobenius + structural bit-decomp + polynomial-form host cache + inline simplification + linear elimination, 2026-05-27):**

Five orthogonal optimisations applied in sequence:

1. **Frobenius-aware reduction in Buchberger** (commit `d864305fbd`):
   bit-variable exponents clamped to 1 after every polynomial
   operation. 70–1000× speedup on bit-decomp queries.
2. **Structural bit-decomposition** (commit `61faaf0f29` part 1):
   `decompose_bits()` now recursively computes bit polynomials
   directly for `bvnot`, `bvshl`, `bvlshr`, `bvand`, `bvor`,
   `bvxor`, constants — without going through a fresh host. Eager
   Frobenius applied during construction.
3. **Polynomial-form host cache** (commit `61faaf0f29` part 2):
   syntactically-different-but-semantically-equal compounds (like
   `a+b` and `b+a`) share a host.
4. **Inline idempotency simplification in polynomial multiplication**
   (commit `50252003e4`): `polynomialt::multiply(other, bit_vars)`
   clamps bit-variable exponents during the term-pair loop.
   Neutral on the test suite (the bottleneck wasn't here);
   kept as a clean infrastructure improvement.
5. **Linear elimination of host variables** (commit `a54fa27f04`):
   substitutes each host $h$ with its bit-sum polynomial
   $\sum_i 2^i b_i$ BEFORE Buchberger and BEFORE the vanishing-
   polynomial test. This was the missing piece — the actual
   bottleneck was the vanishing-polynomial test on bit-decomp
   queries (Stirling matrix / Kronecker product exponential in
   the number of bit variables). Linear elimination collapses
   the diff polynomial to zero, the vanishing test recognises
   trivial vanishing, and we report UNSAT directly.

Empirical impact:

| Query | Bitwidth | MVP (Frobenius only) | After all 5 optimisations |
|---|---|---|---|
| `(a XOR b) XOR b = a` | 4 | 0.03 s | **0.00 s** |
| `(a XOR b) XOR b = a` | 16 | T/O 30 s | **0.00 s** |
| `(a XOR b) XOR b = a` | 32 | T/O 30 s | **0.01 s** |
| `(a XOR b) XOR b = a` | 64 | (untested) | **0.02 s** |
| `(a XOR b) XOR b = a` | 128 | (untested) | **0.07 s** |
| De Morgan | 16 | T/O 30 s | **0.00 s** |
| De Morgan | 64 | (untested) | **0.02 s** |
| De Morgan | 128 | (untested) | **0.08 s** |
| `((a+b)>>1) = ((b+a)>>1)` | 32 | (impractical) | **0.00 s** |
| `((a+b)-(a-b))>>1 = b ∧ b<128` | 8 | (untested) | **0.00 s** |
| `((a+b)+(c+d))>>2 = ((a+c)+(b+d))>>2` | 16 | (untested) | **0.00 s** |

**Linear scaling** (~$O(d)$) in bitwidth on these queries.
Re 4 sub-goal 3 is essentially complete. The procedure with
bit-decomposition is tractable on production-scale bitwidths
for queries with reasonable polynomial structure.

**Then (Re 4 sub-goals 4, 5, 6):** with sub-goal 3 essentially
complete, faithful Toom-Cook 4-way SABER and GRS-128 are
**reachable for production-scale bitwidths**. Universal-
relational queries (sub-goal 6) still require a separate
`bvult` / `bvslt` encoding design.

**Updated sequencing (2026-05-27 evening):**

- **DONE this session**: Re 4 MVP, sub-goal 3 (Frobenius +
  structural decomp + polynomial-form cache + inline
  simplification + linear elimination), sub-goal 4 attempt
  (Toom-Cook 4-way generator implemented; verification
  intractable, identified as open challenge), sub-goal 5
  attempt (GRS investigated, found not to exercise our
  contribution; §4.6 of paper.tex dropped). A (Re 4 paper
  subsection §4.6) committed at `2049316564`. B (§4.3 SABER
  context refresh) committed at `2049316564`. **D (Re 4
  sub-goal 6: universal-relational class via bvult/bvule)**
  implemented at `3fbc1d9c6f`; paper §4.6 updated at
  `889efe9588`. **C (memory-efficient extraction via deferred
  bit-blasting + streaming polynomial multiplication)**
  implemented at `c9f2f825ba`; paper §4.3 updated at
  `49178650da`.
- 2026-05-27 → 2026-06-02: holding pattern (peer review
  feedback on Paper 1).
- 2026-06-02 → 2026-08-15 (~10 weeks): **post-D/C polish and
  follow-on items**, in priority order:
    1. ~~**Make DEFER\_BITBLAST the default**~~ — DONE this
       session at `d6f3c405a4`. Re 4 sub-goal 7 is now on by
       default; DISABLE\_DEFER\_BITBLAST=1 opts out for
       ablation. 100+ smt-comp benchmark regression validates
       correctness.
    2. **Bit-by-bit parity reasoning** for shift identities
       (currently the toom-scaled query TOs because Buchberger
       cannot align `2b mod 2^d = sum 2^i b_h_i` position-by-
       position). Either parity-aware reduction ordering or
       extractor-induced bit alignments. Could close §4.6's
       remaining scope-limit caveat.
    3. **Sub-goal 6 follow-ons**: signed comparisons (bvslt /
       bvsle); symbol-symbol comparisons; chain-encoding
       optimisation at bw=128 (currently TOs on the lower-bound
       chain at bw=128).
    4. **Faster polynomial multiplication for SABER >N=768**
       (Toom-Cook style multiplication of polynomial-system
       polynomials, or specialised Buchberger orderings). The
       N=1024+ time-bound ceiling can be pushed.
- 2026-08-15 → 2026-09-30 (~6 weeks): paper final pass.
- 2026-10-15: TACAS 2027 deadline.

Toom-Cook 4-way SABER verification (faithful schoolbook =
Toom-Cook 4-way) remains a post-paper open challenge. Theory
combination (Re 8) remains post-paper future direction.

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
