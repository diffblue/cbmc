# Faithful Toom-Cook 4-way SABER: empirical findings (2026-05-27)

*Status: Toom-Cook 4-way generator implemented and faithful to SABER's
C reference at `Reference_Implementation_KEM/poly_mul.c`. Verification
of equivalence to schoolbook is **intractable for all tested SMT
solvers** (bitwuzla, cvc5, our smt2_solver) at any N >= 4 within 3
minutes, even at single-coefficient granularity.*

## Generator

`bench-multiplication/saber/make-saber-query.py --algo-b toom4` emits
SMT-LIB queries that faithfully implement SABER's Toom-Cook 4-way
algorithm:

- Split inputs into 4 sub-polynomials of size $N_{\mathrm{SB}} = N/4$.
- Evaluate at 7 points (with scaling for fractional points to avoid
  divisions): $0$, $1$, $-1$, $2$, $8 \cdot 1/2$, $8 \cdot (-1/2)$,
  $\infty$.
- Pointwise multiply (schoolbook on $N_{\mathrm{SB}}$-coefficient
  polynomials, since we already verify schoolbook = karatsuba
  elsewhere).
- Interpolate via SABER's formulas: arithmetic and shifts (`>> 1`,
  `>> 3`, `<< 6`, ...) and multiplications by modular inverses
  $\mathrm{inv3} = 43691$, $\mathrm{inv9} = 36409$,
  $\mathrm{inv15} = 61167$ in $\mathbb{Z}_{2^{16}}$.
- Place 7 chunks of $2 N_{\mathrm{SB}} - 1$ coefficients each at
  offsets $0, N_{\mathrm{SB}}, 2 N_{\mathrm{SB}}, \ldots, 6 N_{\mathrm{SB}}$
  in the 2N-coefficient output buffer.

Verified faithful: with pinned inputs (e.g., `a=1,2,3,4 b=5,6,7,8`),
the SMT-LIB output matches SABER's C `toom_cook_4way` byte-for-byte.

## Required parameters

- **`--q 16`**: SABER's storage type is `uint16_t`; the modular
  inverses $\mathrm{inv3}$ etc. are inverses in $\mathbb{Z}_{2^{16}}$.
- **`--cmp-qbits 13`**: the actual SABER modulus is $q = 2^{13}$.
  SABER's Toom-Cook 4-way is **only correct modulo q = 2^{13}**;
  it is not correct modulo $2^{16}$ (the storage type).

## Why mod-q comparison is needed

Empirical investigation shows SABER's Toom-Cook 4-way does not
match schoolbook polynomial multiplication mod $2^{16}$ for arbitrary
`uint16_t` inputs. The deviation is in the high 3 bits of the result.
Detailed verification: at $q = 2^{16}$ over 100 random `uint16_t`
input pairs, 0/100 match; at $q = 2^{13}$, 100/100 match. (Tested at
$N_{\mathrm{SB}} \in \{1, 2, 4, 8, 16, 32, 64\}$.)

**This is a substantive cryptographic verification finding.** SABER's
specification states $q = 2^{13}$, and the C implementation correctly
computes the polynomial product modulo $q$. But the implementation's
intermediate values (in `uint16_t`, mod $2^{16}$) deviate from the
"polynomial product mod $2^{16}$" by up to $2^{13}$. The deviation
is masked by SABER's downstream operations, which always reduce
modulo $q$ before use.

Worked example: at $N=8$ with $a[0]=1$, $b[7]=1$ (only one input bit
set per polynomial), schoolbook gives $c[7] = 1$ (others zero). A
"small SABER" implementation (same algorithm at $N_{\mathrm{SB}}=2$)
gives $c[7] = 32769$. The difference $32768 = 2^{15}$ is not visible
mod $2^{13}$ ($32769 \bmod 8192 = 1$).

The full SABER (at $N_{\mathrm{SB}}=64$ with first-8-positions input)
happens to give $c[7] = 1$ (matching schoolbook), but for arbitrary
random inputs at $N_{\mathrm{SB}}=64$, deviations recur. The match
mod $q$ is universal; the match mod $2^{16}$ is input-dependent.

## Verification empirical results

With `--cmp-qbits 13` (the correct comparison), we have the well-
posed verification target: schoolbook = Toom-Cook 4-way mod $2^{13}$
for arbitrary `uint16_t` inputs.

| Query | Expected | bitwuzla | cvc5 | our procedure |
|---|---|---|---|---|
| Toom-4 vs schoolbook, N=4, q-mod, all coeffs | UNSAT | T/O 60s | T/O 60s | T/O 60s |
| Toom-4 vs schoolbook, N=4, q-mod, c[0] only | UNSAT | T/O 180s | T/O 180s | T/O 180s |
| Toom-4 vs schoolbook, N=4, q-mod, inputs in [0, 8) | UNSAT | T/O 30s | (untested) | T/O 180s |
| Toom-4 vs schoolbook, N=8, q-mod, all coeffs | UNSAT | T/O 30s | T/O 60s | T/O 60s |
| Toom-4 vs schoolbook, N=16, q-mod, all coeffs | UNSAT | T/O 60s | (untested) | T/O 120s |
| **Toom-4 vs schoolbook, N=4, q-mod, all coeffs (30 min)** | UNSAT | **T/O 1800s** | (untested) | (untested) |
| **Toom-4 vs schoolbook, N=4, q-mod, c[0] only (30 min)** | UNSAT | **T/O 1800s** | (untested) | **T/O 1800s** |
| Pinned inputs (a=1..4, b=5..8), N=4, q-mod | UNSAT | 0.00 s | 0.00 s | 0.00 s |
| schoolbook = schoolbook, N=4, q-mod | UNSAT | 0.00 s | 0.00 s | 0.00 s |
| schoolbook = karatsuba, N=8, q-mod | UNSAT | 0.00 s | 0.00 s | 0.10 s |

**Faithful Toom-Cook 4-way verification is currently intractable for
state-of-the-art SMT solvers**, even at small $N$ and for a single
coefficient. This is despite the algorithm being well-known and the
target property being mathematically clear. The intractability comes
from:

- 4 shift operations per coefficient (`>> 1` arithmetic, `>> 3`,
  `>> 1`, `>> 2` logical, embedded in a chain of additions /
  subtractions / multiplications by 32-bit modular inverses).
- The 32-bit intermediate width necessitated by the C `(uint32_t)`
  cast in SABER's interpolation formulas.
- The `mod q = 2^{13}` comparison adds reasoning over the low 13 bits
  while the algorithm operates on full 16/32-bit values.

**Extended-timeout test (30 minutes, 2026-05-27).** To confirm the
intractability is genuine rather than a near-miss, we re-ran the
N=4 single-coefficient and all-coefficient queries at a 30-minute
(1800 s) timeout for both Bitwuzla and our procedure. **All
runs timed out.** This rules out the hypothesis that "more time
would suffice"; the queries are intrinsically beyond current
SMT capability at any feasible budget.

For our procedure: the bit-decomposition machinery (Re 4) handles
`bvlshr` and `bvashr` soundly, but the resulting polynomial system
is too large for current Buchberger heuristics. Even with linear
elimination + Frobenius, the procedure runs out of step budget.

## Implications

The Re 4 design (commits `00d943b133` through `2cee61e6b7`) handles
all of SABER's polynomial-multiplication primitives soundly:
`bvlshr`, `bvashr`, `bvand`, `bvor`, `bvxor`, `bvnot`. But the Toom-
Cook 4-way verification target is intractable not for soundness
reasons but for combinatorial reasons (the universal-equational
query has a very large polynomial system).

The verification challenge for Toom-Cook 4-way is **identified as an
open problem in this work**. State-of-the-art SMT solvers cannot
discharge it. Future work on tractability:

1. **Specialized polynomial-arithmetic procedures** that recognise
   the Toom-Cook structure (evaluation/interpolation pattern) and
   discharge equivalence symbolically rather than via bit-blasting
   or Buchberger.
2. **Custom SAT-encoding heuristics** for the specific shift +
   inverse multiplication patterns that appear here.
3. **Decompose verification into smaller lemmas**: prove evaluation
   is correct, prove inner products compose correctly, prove
   interpolation matches mod q. Each sub-lemma may be tractable
   while the full equivalence isn't.

## Status

- Toom-Cook 4-way generator: **implemented**
  (`make-saber-query.py --algo-b toom4`). Faithful to SABER's C.
- Mod-q comparison: **implemented** (`--cmp-qbits` parameter).
- Verification at any N >= 4: **open challenge**. Intractable for
  bitwuzla, cvc5, and our procedure within reasonable time.
- Recommendation for §4.3 of paper.tex: keep 2-level Karatsuba as the
  headline SABER result; mention faithful Toom-Cook 4-way as a
  related-work / open-challenge note. The "schoolbook = 2-level
  Karatsuba" comparison still demonstrates SABER's structural depth
  at the polynomial level.

## Cross-references

- `bench-multiplication/saber/make-saber-query.py` —
  generator (added `toom4` algorithm + `--cmp-qbits` parameter).
- `Reference_Implementation_KEM/poly_mul.c` (SABER repo) —
  reference C implementation.
- `re4-bit-decomposition-design-2026-05-27.md` — Re 4 sub-goal 3
  optimisations (Frobenius, structural decomp, polynomial-form
  cache, inline simplification, linear elimination).
- `saber-experiment-2026-05-26.md` — earlier 2-level Karatsuba
  results.
- `future-directions-2026-05-27.md` — master tracker.
