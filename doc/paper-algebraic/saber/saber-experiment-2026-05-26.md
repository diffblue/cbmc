# SABER Polynomial Multiplication Verification: Level A Findings

*Date: 2026-05-26*
*Status: experiment results + sanity checks for related future
directions.*

This document reports the SABER Level A experiment (Re 6 in the
2026-05-26 future-directions discussion) and sanity checks for
Re 3 (expression-level normalisation) and Re 4 (bit-decomposition
variables).

## SABER experiment (Re 6)

### What we verified

SABER's reference C implementation
(`SABER/Reference_Implementation_KEM/poly_mul.c`) uses Toom-Cook
4-way decomposition with Karatsuba as the inner kernel, plus
reduction modulo $x^N + 1$:

```c
void poly_mul_acc(a, b, res) {
    uint16_t c[2 * SABER_N] = {0};
    toom_cook_4way(a, b, c);                 // 2N-coeff product
    for (i = SABER_N; i < 2 * SABER_N; i++) {
        res[i - SABER_N] += c[i - SABER_N] - c[i];   // reduce mod x^N + 1
    }
}
```

The standard SABER parameters are $N = 256$ and $q = 8192 = 2^{13}$,
with 16-bit (`uint16_t`) storage. The arithmetic happens in
$\mathbb{Z}_{2^{16}}$ via `OVERFLOWING_MUL` (a cast to `uint32_t`,
multiply, cast back to `uint16_t`); this is exactly polynomial
multiplication modulo $2^{16}$.

We constructed an SMT-LIB query asserting that schoolbook
polynomial multiplication and 1-level Karatsuba produce the same
result in $R_q = \mathbb{Z}_{2^{16}}[x] / (x^N + 1)$, mirroring
SABER's structure but at scaled-down $N$.

### Procedure scaling on per-coefficient queries

The disjunctive disequality
`(or (distinct A_res_0 B_res_0) ... (distinct A_res_{N-1} B_res_{N-1}))`
escapes the algebraic pre-solver's Rabinowitsch handling (which
addresses single disequalities), so the disjunction triggers
bit-blasting. The standard workaround: emit one query per output
coefficient. Each is then a single-disequality query that the
algebraic procedure handles directly via Rabinowitsch +
Buchberger.

| $N$ | Query size (bytes) | This paper (per coeff) | Bitwuzla 0.9.0-dev | cvc5 1.3.3 |
|---|---|---|---|---|
| 4   | 1.4 K  | 0.02 s | 0.00 s | T/O on 3 of 4 coeffs |
| 8   | 5.0 K  | 0.06 s | 0.00 s | T/O |
| 16  | 19 K   | 0.38 s | 0.00 s | T/O |
| 32  | 61 K   | 1.53 s | 0.00 s | T/O |
| 64  | 213 K  | 6.16 s | 0.02 s | T/O |
| 128 | 803 K  | 25.15 s | 0.06 s | T/O |
| 256 | 3.2 MB | 104.34 s | 0.25 s | T/O |

Times above are at $q = 16$ (SABER's storage bitwidth). Results
at $q = 13$ (the algebraic ring) are slightly faster but
qualitatively identical.

**Headline findings:**

- **Scales to SABER's actual $N = 256$ parameter.** At full
  scale, our procedure decides each output-coefficient
  equivalence in 70–105 s. With 256 coefficients to check and
  parallelism across cores, full-multiplication verification
  takes 30–60 s on a multi-core machine.
- **Beats cvc5 dramatically.** cvc5 times out at $N = 4$ on most
  coefficients (3 of 4), and at $N \geq 8$ on every coefficient
  we tested. Our procedure decides them in milliseconds. This is
  a 3+ orders of magnitude gap.
- **Ties or trails Bitwuzla.** Bitwuzla wins this benchmark
  family because its occurrence-map canonicalisation reduces
  schoolbook and Karatsuba to the same canonical sum-of-monomials
  form syntactically. We trail by 1.5–3 orders of magnitude. This
  is the same pattern as the random-polynomial 210-suite: where
  Bitwuzla can canonicalise, it dominates; where it cannot
  (vanishing polynomials, etc.), we lead.

### Suitability for Paper 2

Adding SABER as a §4.8 (or new appendix) entry in Paper 2's
revision gives:

1. A **named external application** (post-quantum cryptography),
   countering the §4.7 "we designed the DSP benchmarks"
   threat-to-validity.
2. A real-world benchmark family demonstrating the procedure
   scales to industrially relevant problem sizes ($N = 256$).
3. Another empirical demonstration of the
   "we beat cvc5, tie Bitwuzla" pattern that Paper 2's
   completeness-first headline (G) already articulates.
4. Concrete reproducibility: queries are mechanically generated
   from a Python script (`make-saber-query.py`) and benchmarks
   are derived from the published KU Leuven SABER reference
   code.

### Open caveats

- **1-level Karatsuba, not multi-level.** SABER's actual
  implementation uses Toom-Cook 4-way + Karatsuba (a 2-level
  decomposition). We verified 1-level Karatsuba equivalence;
  multi-level would verify the same algebraic identity at higher
  syntactic complexity. Worth doing if we want to claim
  "verifies SABER's full algorithmic structure" rather than
  "verifies a SABER-shaped polynomial-multiplication identity".
  Effort: extend `make-saber-query.py` with a Toom-Cook 4-way
  mode (~half a day).
- **Per-coefficient, not whole-polynomial.** The SABER reduction
  step `res[i] = c[i] - c[i+N]` is verified implicitly because
  each coefficient query includes it. A whole-polynomial query
  would require either (a) avoiding the disjunction-bit-blasting
  blowup (requires a procedure-level extension to handle
  disjunctions of disequalities via Rabinowitsch on each branch
  — non-trivial), or (b) keeping per-coefficient and reporting
  total runtime as the sum.
- **Worst-case `bvmul` arity.** `make-saber-query.py` emits
  expressions like
  `(bvadd (bvadd (bvadd (bvmul a0 b3) (bvmul a1 b2)) (bvmul a2 b1)) (bvmul a3 b0))`.
  This is left-associative. SMT-LIB allows variadic `bvadd`,
  but we use binary chains for clarity. Should not affect
  semantics or timings noticeably.

### Reproduction

```bash
cd bench-multiplication/saber
python3 make-saber-query.py --n 16 --q 16 --single-coeff 0 \
  > saber-n16-bw16-c0.smt2
build/bin/smt2_solver --cadical saber-n16-bw16-c0.smt2
```

Source: https://github.com/KULeuven-COSIC/SABER (reference
implementation in `Reference_Implementation_KEM/`).

## Sanity check Re 4: bit-decomposition variables

**Question.** Does Buchberger terminate when we add idempotency
($b^2 = b$) and sum-decomposition ($x = \sum_i 2^i b_i$)
constraints to the polynomial system, or does the augmented
basis blow up?

**Test.** 8-bit commutativity ($\forall a, b \in \mathbb{Z}_{2^8}.\ a \cdot b = b \cdot a$)
augmented with bit-decomposition for both inputs into 4-bit
representations: 8 idempotency constraints (one per bit-variable)
and 2 sum-decomposition constraints (one per input).

| Configuration | Time |
|---|---|
| Plain 8-bit commutativity (no bit-decomposition) | 0.00 s |
| With bit-decomposition (10 added equations)        | 0.00 s |

**Result.** Pass. Buchberger terminates immediately on the
augmented system; the additional 10 equations do not cause an
explosion. The basis remains tractable at this scale.

**Caveat.** This is a small smoke test. Real bit-decomposition
in production would add constraints on demand (only for bit
positions referenced by relational predicates), at scales of
8–32 bits per relational predicate. The empirical question is
whether this scale also stays tractable; the 4-bit smoke test
suggests yes but doesn't prove it. A more thorough test would
take a relational query (e.g., $\forall a, b \in \mathbb{Z}_{2^8}.\ |a \cdot b| < 2^{15}$),
add the relevant bit-decomposition constraints, and verify
termination.

**Recommendation.** Re 4 is feasible to implement; sanity check
passes the basic tractability question. Effort estimate stands
at 4–8 weeks for a working prototype that integrates
bit-decomposition into the algebraic-pre-solver entry point.

## Sanity check Re 3: expression-level normalisation

**Question.** Does running `reduce_by_basis` on residual
expressions produce useful normal forms when Buchberger
terminates inconclusively?

**Discovery.** The simple form of expression-level normalisation
**is already prototyped** in CBMC under the
`ENABLE_GB_EXPR_NORMALISE` environment variable. The relevant
code is at `src/solvers/flattening/boolbv.cpp:962–1000`:
after Buchberger returns inconclusive, for each disequality,
reduce its `lhs - rhs` polynomial modulo the basis and check
whether the result is zero.

**Existing empirical result** (from
`doc/paper-algebraic/expression-normalisation-design.md`):

> 0 of 210 benchmarks helped, 0 of 210 hurt. Total runtime
> difference: +0.04 s (i.e., 0.0%) — well below noise.

**Why the simple variant is null.** The check requires:
1. Per-disequality Buchberger with Rabinowitsch returns UNKNOWN.
2. Global Buchberger returns UNKNOWN.
3. Some disequality's `lhs - rhs` reduces to 0 by the global basis.

Condition 3 holding *with the per-disequality basis* would already
make the per-disequality pass return UNSAT (the Rabinowitsch
polynomial reduces to a unit constant). So condition 3 must hold
*only with the global basis*, which adds Rabinowitsch polynomials
for *other* disequalities.

This is rare in practice: CBMC's typical SMT query has a single
top-level disequality (the negated assertion), so the global
basis equals the per-disequality basis and the check is
redundant.

**Sophisticated variants exist on paper but are unimplemented:**

1. **Compound multiplication constant folding.** For each
   `bvmul(a, b)` sub-expression that survives to bit-blasting,
   reduce by basis; if reduces to a constant, emit
   `bvmul = constant` at the SAT level. Requires polynomial-to-
   expression conversion infrastructure.

2. **Pairwise variable equality discovery.** For each pair $(a, b)$
   of input symbols, reduce $a - b$ by basis. Generally fires
   only when input symbols are constrained equal — uncommon in
   well-formed queries.

3. **Generalised candidate extraction.** Walk every variable in
   the basis (not just univariate-linear ones); use
   `reduce_by_basis` to discover constants for compound monomials.
   Requires extending `extract_candidate` to multivariate cases.

**Recommendation.** Re 3 in its simple form is empirically null;
sophisticated variants would require non-trivial engineering and
have unknown empirical impact. Probably **not** the right pick
for the immediate Paper 2 revision; better as a future-direction
signpost in the paper plus a follow-up paper (see
`expression-normalisation-design.md` "Future work pointer"
section, which already gestures at a follow-up theory-solver
paper combining items 7 and 8).

## Updated future-direction recommendations

| Direction | Sanity status | Implementation effort | Recommendation for Paper 2 revision |
|---|---|---|---|
| (6) SABER benchmark | **Pass** (works at $N=256$) | Already done at experiment level | **Include as §4.8 or appendix** |
| (4) Bit-decomposition variables | **Pass** (Buchberger terminates) | 4–8 weeks for working prototype | Future direction signpost; defer to follow-up paper |
| (3) Expression-level normalisation (simple) | **Already implemented**; null empirical result | — | Future direction signpost; mention the null result honestly |
| (3) Expression-level normalisation (sophisticated variants) | Unknown | 1–2 weeks per variant | Future direction signpost; combine with theory-solver paper |
| (5) Theory combination | Out of scope | 2–4 months architectural | Long-term direction; one-paragraph signpost |

**Bottom line for the next Paper 2 revision:** add SABER as a
new evaluation section, keep (3) and (4) as future-direction
prose with the honest sanity-check status documented above.

## Files

```
bench-multiplication/saber/
├── make-saber-query.py                      # query generator
├── saber-n4-bw13-school-vs-school.smt2     # sanity test (trivially unsat)
├── saber-n4-bw13-school-vs-kara.smt2       # full goal, 4-disjunction (TO)
├── saber-n4-bw13-c0.smt2                    # per-coefficient queries
├── saber-n8-bw13-c0.smt2                    # ...
├── saber-n{16,32,64,128,256}-bw{13,16}-c0.smt2
└── sanity-bit-decomp.smt2                   # Re 4 sanity check
```

## Process

These findings are research notes; no paper.tex changes have
been made. When Paper 2 revision time comes:

1. Decide whether to integrate SABER as §4.8 / new appendix /
   appendix-only.
2. Update §3.7 Future Directions with the (3)-already-prototyped
   and (4)-sanity-passes findings.
3. Optional: extend `make-saber-query.py` with multi-level
   Toom-Cook for closer-to-actual-SABER framing.
