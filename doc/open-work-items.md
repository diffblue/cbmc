# Open Work Items — Tracking Document

## Status Summary

| Item | Status | Priority |
|---|---|---|
| smt2 v4 results analysis | Data collected, needs analysis | High |
| Level 3: Hybrid algebraic + bit-blasting | Detailed plan ready | Medium |
| Floating-point via float_bvt | Investigated, plan needed | Medium |
| Paper finalization for PoS 2026 (May 7) | 13 pages, 28 refs, needs v4 data | High |

---

## 1. smt2 v4 Results Analysis

### Data
- File: `bench-multiplication/smt2-results-v4-clean.tsv`
- 1728 jobs, median of 3 runs, 120s timeout
- 412 T/O (down from 556 in v3 = 144 more benchmarks solved)
- v3 had no Gröbner basis for assoc/distrib; v4 has the full
  algebraic solver with equation ordering fix

### Analysis needed
1. Compare v4 vs v3 on polynomial equation benchmarks (comm, assoc,
   distrib): expect <10ms in v4 vs seconds/T/O in v3
2. Verify no regressions on non-polynomial benchmarks (overflow,
   keyed_hash, hw_mul_equiv)
3. Cross-solver comparison: the Gröbner basis runs before the SAT
   solver, so all 4 solvers should show identical times on polynomial
   benchmarks (the solver choice becomes irrelevant)
4. Update paper Table 4 and Table 8 if v4 numbers differ significantly

### Expected outcome
The Gröbner basis makes the multiplier encoding AND solver choice
irrelevant for polynomial equation benchmarks. This is the strongest
possible result — it means the algebraic solver subsumes all the
encoding optimization work for this problem class.

---

## 2. Level 3: Hybrid Algebraic + Bit-Blasting

### Detailed plan
See `doc/algebraic-methods-investigation.md`, section
"Level 3: Hybrid Algebraic + Bit-Blasting (Detailed Plan)".

### Summary
Four implementation steps (~310 lines total):
1. **Candidate extraction** from Gröbner basis (~50 lines):
   Walk reduced basis for univariate polynomials, extract assignments
2. **Residual checking** via SAT assumptions (~100 lines):
   Add algebraic candidate as retractable assumptions, check residual
3. **Conflict conversion** to polynomial equations (~80 lines):
   Convert violated inequalities to polynomial equations where possible
4. **Integration** into `bv_refinementt::dec_solve()` (~80 lines):
   Algebraic CEGAR loop before existing SAT-based CEGAR

### Key challenge
Variable mapping between polynomial indices and SAT bit-vectors.
Solution: reverse mapping in `poly_extractort`.

### Target benchmarks
Mixed polynomial + non-polynomial problems:
- `a*b == b*a && a > 100` (commutativity + inequality)
- `a*(b+c) == a*b + a*c && a*b < 1000` (distributivity + inequality)
- Overflow-safe algebraic properties

### Expected impact
Modest for current benchmarks (most are purely polynomial or purely
non-polynomial). Main value: architectural completeness and handling
of future mixed-constraint verification queries.

### Dependencies
All prerequisites implemented (Phases 1-4 of algebraic solver).

---

## 3. Floating-Point via float_bvt

### Discovery
CBMC has two FP encoding paths:
- `float_utilst` (current default): works at bit-vector level (bvt),
  produces SAT clauses directly. The Gröbner basis cannot see the
  algebraic structure.
- `float_bvt`: works at expression level (exprt), produces expression
  trees that are THEN bit-blasted by boolbvt. The expression trees
  contain `mult_exprt` and `plus_exprt` that the Gröbner basis
  extractor CAN handle.

### What float_bvt::mul produces
```
result.fraction = mult_exprt(fraction1, fraction2)  // POLYNOMIAL
result.exponent = plus_exprt(exponent1, exponent2)  // POLYNOMIAL
result.sign = notequal_exprt(sign1, sign2)           // non-polynomial (XOR)
result.infinity = or_exprt(inf1, inf2)               // non-polynomial
result.NaN = disjunction(...)                        // non-polynomial
```

The mantissa multiplication and exponent addition are pure polynomial
operations. The sign, infinity, and NaN handling are non-polynomial
but structurally simple.

### Opportunity
For FP multiplication commutativity (`a *_fp b == b *_fp a`):
- Mantissa: `frac1 * frac2 == frac2 * frac1` → Gröbner basis (instant)
- Exponent: `exp1 + exp2 == exp2 + exp1` → Gröbner basis (instant)
- Sign: `sign1 ≠ sign2 == sign2 ≠ sign1` → word-level simplification
- NaN/infinity: symmetric conditions → word-level simplification

FP multiplication commutativity could be proven entirely algebraically
at any precision — no bit-blasting of the mantissa multiplication.

### Implementation plan
1. **Make FP encoding path configurable**: add option to use `float_bvt`
   instead of `float_utilst` in `boolbv_floatbv_op.cpp`
   - `float_bvt::convert()` returns an `exprt` that goes through
     `boolbvt::convert_bv()` → `set_to()` → Gröbner basis extractor
   - The polynomial parts (mantissa mult, exponent add) are extracted
   - The non-polynomial parts (sign, NaN, infinity, rounding) fall
     through to bit-blasting

2. **Verify on FP benchmarks**:
   - FP multiplication commutativity: expect instant (Gröbner basis)
   - FP addition commutativity: more complex (alignment shift is
     non-polynomial), may still need bit-blasting
   - FP determinism (hash functions): mixed, depends on operations

3. **Integration with Level 3**: The non-polynomial FP parts (sign XOR,
   rounding) are the "residual" that Level 3's CEGAR loop would handle.
   With float_bvt + Level 3, FP verification could be decomposed into:
   - Algebraic part (mantissa, exponent) → Gröbner basis
   - Residual part (sign, rounding, NaN) → bit-blasting
   - CEGAR loop connects them

### Key files
- `src/solvers/floatbv/float_bv.h` — expression-level FP encoding
- `src/solvers/floatbv/float_bv.cpp` — mul, add, div implementations
- `src/solvers/flattening/boolbv_floatbv_op.cpp` — integration point
  (currently uses float_utilst, would need float_bvt option)

### Risk assessment
- **Low risk**: Making the encoding path configurable is straightforward
- **Medium risk**: float_bvt may produce larger expression trees than
  float_utilst (more intermediate variables), potentially slower for
  non-algebraic FP problems
- **High risk**: FP addition commutativity involves the barrel shifter
  (alignment shift by variable amount), which is inherently non-polynomial.
  The Gröbner basis would only help with the mantissa addition, not
  the alignment. The barrel shifter is the 28× hardness source we
  identified earlier.

### Expected impact
- FP multiplication commutativity: HIGH (instant at any precision)
- FP addition commutativity: LOW (barrel shifter dominates)
- FP determinism: MEDIUM (depends on which operations are used)

---

## 4. Paper Status

### Current state
- 13 pages, 28 references
- Four-layer defense table (Table 9) with cbmc and smt2 columns
- Gröbner basis as contribution #4
- All key results documented

### Remaining for PoS submission (May 7)
1. Update with v4 smt2 data (if numbers differ significantly)
2. Final proofread
3. Author list finalization
4. Submission logistics

### Potential additions (if time permits)
- Level 3 results (if implemented before deadline)
- float_bvt results (if implemented before deadline)
- Both would strengthen the paper but are not required — the
  four-layer defense story is already complete
