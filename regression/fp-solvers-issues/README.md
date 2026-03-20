# Floating-Point Solver Issues: CBMC Analysis

This document tracks known floating-point issues from external SMT solvers
(Z3, CVC5, Bitwuzla) and documents whether CBMC's own SMT solver and
verification pipeline are affected by similar problems.

## Status Legend

- **Not Started**: Issue not yet analyzed for CBMC
- **Analyzed**: Issue reviewed, CBMC behavior determined
- **Test Added**: Regression test(s) committed
- **N/A**: Issue not applicable to CBMC (e.g., involves features CBMC doesn't support)

---

## Z3 Issues (from `Floats` label)

### Explicitly Listed Issues (from fp_issues.txt)

| # | Z3 Issue | Title | Z3 Status | Category | CBMC Status |
|---|----------|-------|-----------|----------|-------------|
| 1 | [Z3#6728](https://github.com/Z3Prover/z3/issues/6728) | Inconsistent answers on NaN and uninterpreted functions | Closed | Soundness (NaN equality vs UF) | Test Added ✅ |
| 2 | [Z3#7162](https://github.com/Z3Prover/z3/issues/7162) | Invalid model on float formula | Open | Invalid model (fp.sub/fp.fma with RNA/RTN) | Test Added ✅ (fp.sub only; fp.fma unsupported) |
| 3 | [Z3#7321](https://github.com/Z3Prover/z3/issues/7321) | Invalid model issue on floats | Open | Invalid model (fp.to_real + fp.eq) | Analyzed — fp.to_real unsupported |
| 4 | [Z3#7842](https://github.com/Z3Prover/z3/issues/7842) | Incorrect model (NaN + datatype) | Open | Invalid model (NaN distinct + datatype) | Not Started |
| 5 | [Z3#8097](https://github.com/Z3Prover/z3/issues/8097) | Segfault with exists-quantified QF_FP + UF | Closed | Crash (segfault) | Not Started |
| 6 | [Z3#8169](https://github.com/Z3Prover/z3/issues/8169) | Incorrect model with (_ FloatingPoint 2 24) and fp.to_real | Closed | Invalid model (non-standard FP sort + fp.to_real) | Analyzed — fp.to_real unsupported |
| 7 | [Z3#8282](https://github.com/Z3Prover/z3/issues/8282) | Performance slowdown on equivalent SMT2 files | Closed | Performance | N/A (performance only) |
| 8 | [Z3#8345](https://github.com/Z3Prover/z3/issues/8345) | Soundness issue converting bit repr to fp to Real | Closed | Soundness (int2bv + to_fp + fp.to_real + incremental) | Analyzed — fp.to_real unsupported, no incremental |
| 9 | [Z3#8414](https://github.com/Z3Prover/z3/issues/8414) | Assertion violation in mpf.cpp (fp.rem) | Closed | Crash (assertion violation in fp.rem) | Test Added ✅ (no crash) |

### Additional Z3 Floats-Labeled Issues

| # | Z3 Issue | Title | Z3 Status | Category | CBMC Status |
|---|----------|-------|-----------|----------|-------------|
| 10 | [Z3#8185](https://github.com/Z3Prover/z3/issues/8185) | Incorrect model in mixed FP/Real logic + string constraint | Open | Invalid model | Not Started |
| 11 | [Z3#8183](https://github.com/Z3Prover/z3/issues/8183) | Incorrect UNSAT in Real-to-FP conversion with RNE/RNA overflow | Closed | Refutational soundness | Not Started |
| 12 | [Z3#7431](https://github.com/Z3Prover/z3/issues/7431) | Invalid model issue on float formula | Open | Invalid model | Not Started |
| 13 | [Z3#7135](https://github.com/Z3Prover/z3/issues/7135) | Refutational soundness issue | Open | Refutational soundness | Not Started |
| 14 | [Z3#7056](https://github.com/Z3Prover/z3/issues/7056) | fp.roundToIntegral gives invalid zero_extend application | Closed | Crash/error | Not Started |
| 15 | [Z3#7026](https://github.com/Z3Prover/z3/issues/7026) | [consolidated] new core, floats | Open | Consolidated | Not Started |
| 16 | [Z3#6983](https://github.com/Z3Prover/z3/issues/6983) | Refutation unsoundness on QF_AFP | Closed | Refutational soundness | Not Started |
| 17 | [Z3#6974](https://github.com/Z3Prover/z3/issues/6974) | Unsoundness with floats | Closed | Soundness | Not Started |
| 18 | [Z3#6972](https://github.com/Z3Prover/z3/issues/6972) | Regression with floats | Closed | Regression | Not Started |
| 19 | [Z3#6970](https://github.com/Z3Prover/z3/issues/6970) | Refutation unsoundness on QF_AFP | Closed | Refutational soundness | Not Started |
| 20 | [Z3#6861](https://github.com/Z3Prover/z3/issues/6861) | Invalid model on incremental FP instance | Closed | Invalid model (incremental) | Not Started |
| 21 | [Z3#6674](https://github.com/Z3Prover/z3/issues/6674) | Assertion violation at mpf.cpp:1966 | Closed | Crash | Not Started |
| 22 | [Z3#6633](https://github.com/Z3Prover/z3/issues/6633) | Problem in Float to Real conversion | Open | fp.to_real | Not Started |
| 23 | [Z3#6553](https://github.com/Z3Prover/z3/issues/6553) | Fuzz bugs for floats - unsoundness / invalid model | Closed | Soundness | Not Started |
| 24 | [Z3#6548](https://github.com/Z3Prover/z3/issues/6548) | fpRealToFP and fpToReal fail on trivial problems | Closed | fp.to_real / to_fp from Real | Not Started |
| 25 | [Z3#6464](https://github.com/Z3Prover/z3/issues/6464) | Segfault with tactics | Closed | Crash | Not Started |
| 26 | [Z3#6460](https://github.com/Z3Prover/z3/issues/6460) | Crash with FPA formula | Closed | Crash | Not Started |
| 27 | [Z3#6457](https://github.com/Z3Prover/z3/issues/6457) | [consolidated] assertion violations | Closed | Crash | Not Started |
| 28 | [Z3#6294](https://github.com/Z3Prover/z3/issues/6294) | Performance regression on trivial FP solve | Closed | Performance | Not Started |
| 29 | [Z3#6117](https://github.com/Z3Prover/z3/issues/6117) | [consolidated] issues in FP | Closed | Consolidated | Not Started |
| 30 | [Z3#6079](https://github.com/Z3Prover/z3/issues/6079) | Invalid model issue on fp | Closed | Invalid model | Not Started |
| 31 | [Z3#6078](https://github.com/Z3Prover/z3/issues/6078) | Unsoundness of fp.to_fp with sat.euf=true | Open | Soundness | Not Started |
| 32 | [Z3#5911](https://github.com/Z3Prover/z3/issues/5911) | Assertion violation at mpf.cpp:907 | Closed | Crash | Not Started |
| 33 | [Z3#5769](https://github.com/Z3Prover/z3/issues/5769) | Invalid model for QF_BVFP formula | Closed | Invalid model | Not Started |
| 34 | [Z3#5572](https://github.com/Z3Prover/z3/issues/5572) | FP condition not finding possible solution | Closed | Incompleteness | Not Started |
| 35 | [Z3#5284](https://github.com/Z3Prover/z3/issues/5284) | Assertion error at mpf.cpp:907 | Closed | Crash | Not Started |
| 36 | [Z3#5051](https://github.com/Z3Prover/z3/issues/5051) | Confusing/unexpected reason-unknown with floats | Closed | UX/completeness | Not Started |
| 37 | [Z3#4889](https://github.com/Z3Prover/z3/issues/4889) | [Consolidated] Bugs in FP logic | Closed | Consolidated | Not Started |
| 38 | [Z3#4880](https://github.com/Z3Prover/z3/issues/4880) | Solution soundness bug in FP logic | Closed | Soundness | Not Started |
| 39 | [Z3#4862](https://github.com/Z3Prover/z3/issues/4862) | Invalid model bug in debug build | Closed | Invalid model | Not Started |
| 40 | [Z3#4861](https://github.com/Z3Prover/z3/issues/4861) | Invalid model bug in QF_FP | Closed | Invalid model | Not Started |
| 41 | [Z3#4858](https://github.com/Z3Prover/z3/issues/4858) | Regression invalid model bug in QF_FP | Closed | Invalid model | Not Started |
| 42 | [Z3#4855](https://github.com/Z3Prover/z3/issues/4855) | Invalid model for QF_FP formula | Closed | Invalid model | Not Started |
| 43 | [Z3#4843](https://github.com/Z3Prover/z3/issues/4843) | QF_FP invalid model | Closed | Invalid model | Not Started |
| 44 | [Z3#4841](https://github.com/Z3Prover/z3/issues/4841) | Invalid model for QF_FP formula | Closed | Invalid model | Not Started |
| 45 | [Z3#4673](https://github.com/Z3Prover/z3/issues/4673) | FP exponent saturates rather than becoming infinite | Closed | Soundness (overflow) | Test Added ✅ |
| 46 | [Z3#2631](https://github.com/Z3Prover/z3/issues/2631) | Quantified FPA formula incorrectly SAT with MBQI | Closed | Soundness (quantifiers) | Not Started |
| 47 | [Z3#2596](https://github.com/Z3Prover/z3/issues/2596) | Quantified FPA formula incorrectly SAT | Closed | Soundness (quantifiers) | Not Started |
| 48 | [Z3#2381](https://github.com/Z3Prover/z3/issues/2381) | fp.rem producing incorrect result | Closed | Soundness (fp.rem) | Test Added ⚠️ BUG FOUND |

---

## CVC5 Issues

| # | CVC5 Issue | Title | CVC5 Status | Category | CBMC Status |
|---|------------|-------|-------------|----------|-------------|
| 49 | [CVC5#11139](https://github.com/cvc5/cvc5/issues/11139) | Fatal failure at symfpu traits (fp.div + fp.fma) | Open | Crash (symfpu postcondition) | Test Added ✅ (fp.div only; fp.fma unsupported) |
| 50 | [CVC5#12306](https://github.com/cvc5/cvc5/issues/12306) | OR operation does not commute in BF16 | Open | Soundness (BF16 non-commutativity) | Not Started |
| 51 | [CVC5#12335](https://github.com/cvc5/cvc5/issues/12335) | Fatal failure at symfpu traits with FP logic | Open | Crash (symfpu postcondition) | Not Started |
| 52 | [CVC5#12371](https://github.com/cvc5/cvc5/issues/12371) | Unsat core was satisfiable (to_fp from Real) | Open | Soundness (to_fp from Real + quantifiers) | Analyzed — quantifiers + to_fp from Real N/A |
| 53 | [CVC5#12383](https://github.com/cvc5/cvc5/issues/12383) | Performance slowdown on equivalent SMT2 files | Open | Performance | N/A (performance only) |
| 54 | [CVC5#12387](https://github.com/cvc5/cvc5/issues/12387) | Fatal failure in proof post-processor (FP + quantifiers) | Open | Crash (proof checking) | N/A (proof checking not applicable) |

---

## Bitwuzla Issues

| # | Bitwuzla Issue | Title | Bitwuzla Status | Category | CBMC Status |
|---|----------------|-------|-----------------|----------|-------------|
| 55 | [Bitwuzla#130](https://github.com/bitwuzla/bitwuzla/issues/130) | SymFPU issue on fp.div for non-standard format | Closed | Soundness (fp.div non-standard FP sort) | Test Added ✅ |

---

## Issue Details and SMT-LIB Reproducer Extracts

Below are the key SMT-LIB snippets extracted from each issue, which will form
the basis for CBMC regression tests.

### Z3#6728 — NaN equality vs uninterpreted functions

**Bug**: `(= NaN NaN)` is true (SMT-LIB semantics: `=` is structural equality),
but Z3 incorrectly returns `sat` when the same NaN values are passed through an
uninterpreted function and compared with `=`. The UF translation to bitvectors
doesn't handle NaN canonicalization.

**Reproducer (should be UNSAT)**:
```smt2
(set-logic ALL)
(declare-const c RoundingMode)
(declare-const x Float64)
(declare-sort T 0)
(declare-fun f (Float64) T)
(assert (not (= (f (fp.add c x (_ NaN 11 53)))
              (f (fp.add c (_ NaN 11 53) x)))))
(check-sat)
```

### Z3#7162 — Invalid model with fp.sub + fp.fma (RNA/RTN)

**Bug**: Z3 generates an invalid model for a formula involving `fp.sub` with RNA
rounding and `fp.fma` with RTN rounding on Float64.

**Reproducer (should be SAT with valid model)**:
```smt2
(declare-const a0 (_ FloatingPoint 11 53))
(declare-const a1 (_ FloatingPoint 11 53))
(declare-const a3 (_ FloatingPoint 11 53))
(declare-const a4 (_ FloatingPoint 11 53))
(assert (= (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)
  (fp.sub RNA a4 (fp.fma RTN a3 a1 a0))))
(check-sat)
```

### Z3#7321 — fp.to_real not propagated through fp.eq

**Bug**: `fp.eq s0 s1` is asserted, but `fp.to_real s0` and `fp.to_real s1`
give different results. Z3 doesn't propagate the equality through `fp.to_real`.

**Reproducer (should be UNSAT)**:
```smt2
(declare-fun s0 () (_ FloatingPoint 4 4))
(define-fun s1 () (_ FloatingPoint 4 4) (fp #b0 #b0000 #b001))
(define-fun s2 () Bool (fp.eq s0 s1))
(define-fun s8 () Real (fp.to_real s0))
(define-fun s10 () Real (/ 1.0 512.0))
(define-fun s11 () Bool (= s8 s10))
(define-fun s12 () Bool (not s11))
(define-fun s13 () Bool (and s2 s12))
(assert s13)
(check-sat)
```

### Z3#7842 — NaN distinct with datatypes

**Bug**: Z3 says `sat` but the model assigns `x = Flt(NaN)` while the assertion
says `x` is distinct from `Flt(NaN)`. Involves user-defined datatypes wrapping
FP values.

**Reproducer (should be UNSAT)**:
```smt2
(set-logic ALL)
(declare-datatype Expr ((Flt (getFlt_1 (_ FloatingPoint 8 24)))))
(declare-fun x () Expr)
(assert (distinct x (Flt (_ NaN 8 24))))
(assert (fp.isNaN (getFlt_1 x)))
(check-sat)
```

### Z3#8097 — Segfault with exists + UF + QF_FP

**Bug**: Z3 crashes with segfault on a QF_FP formula with existential quantifier
and uninterpreted function.

**Reproducer**:
```smt2
(set-logic QF_FP)
(declare-fun f (Float32 Float32 Float32) Float32)
(assert
    (exists ((i Float32) (c Float32))
        (fp.eq c
            (f i
                (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))
                (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))))
(check-sat)
```

### Z3#8169 — Invalid model with non-standard FP sort + fp.to_real

**Bug**: Z3 generates invalid model for `(_ FloatingPoint 2 24)` combined with
`fp.to_real` and `fp.add`.

**Reproducer (should be SAT with valid model)**:
```smt2
(declare-const x (_ FloatingPoint 2 24))
(assert (> (fp.to_real (fp.add RNE x (fp (_ bv0 1) (_ bv0 2) (_ bv0 23)))) 1.0))
(check-sat)
```

### Z3#8345 — Soundness issue with int2bv + to_fp + fp.to_real (incremental)

**Bug**: Incremental solving with quantified functions converting integers to
floats via `int2bv` then `to_fp` then `fp.to_real` can prove false.

**Category**: Involves quantifiers and incremental solving — likely N/A for
CBMC's SMT solver but relevant for CBMC as a user of external SMT solvers.

### Z3#8414 — Assertion violation in fp.rem with non-standard FP sort

**Bug**: Z3 debug build crashes with assertion violation in `mpf.cpp` when
computing `fp.rem` on `(_ FloatingPoint 1 37)` values.

**Reproducer**:
```smt2
(assert (fp.isZero (fp.rem
  (fp (_ bv0 1) #b111100110000111111100101110000000011 (_ bv0 1))
  (fp (_ bv0 1) (_ bv1 36) (_ bv0 1)))))
(check-sat)
```

### CVC5#11139 — symfpu postcondition failure (fp.div + fp.fma)

**Bug**: CVC5 crashes with symfpu postcondition failure on a formula involving
`fp.div RTN` of `fp.fma RTP` result on Float64.

**Reproducer**:
```smt2
(declare-const FP_VAR_a (_ FloatingPoint 11 53))
(declare-const FP_VAR_b (_ FloatingPoint 11 53))
(assert (= (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)
  (fp.div RTN (fp.fma RTP FP_VAR_a FP_VAR_a
    (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)) FP_VAR_b)))
(check-sat)
```

### CVC5#12335 — symfpu postcondition failure with quantified FP

**Bug**: CVC5 crashes with symfpu postcondition failure on a quantified FP
formula involving `fp.div`, `fp.eq`, and `fp.gt`.

**Reproducer**:
```smt2
(set-logic FP)
(declare-const x Float32)
(declare-const a Float32)
(assert (forall ((V Float32) (A Float32))
  (or (not (fp.lt V x))
      (not (fp.eq a a))
      (not (fp.gt A (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))
      (not (fp.eq (fp.div RNE A V) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))))))
(assert (fp.geq a (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))
(check-sat)
```

### CVC5#12371 — Unsat core satisfiable (to_fp from Real + quantifiers)

**Bug**: CVC5 reports unsat but the unsat core is satisfiable. Involves
`to_fp` from Real with `fp.isInfinite` guard inside a universal quantifier.

**Reproducer**:
```smt2
(set-logic ALL)
(assert (forall ((x Real))
  (>= 0.0 (ite (fp.isInfinite ((_ to_fp 8 24) RNE x)) x 0.0))))
(check-sat)
```

### CVC5#12387 — Proof post-processor failure (FP + quantifiers)

**Bug**: CVC5 crashes in proof post-processor with `--check-proofs` on a
formula with quantified Float32 and `fp.eq` + `ite` + NaN.

**Reproducer**:
```smt2
(set-logic ALL)
(declare-const x Bool)
(declare-const x1 Bool)
(declare-const x4 Bool)
(declare-const x41 Bool)
(declare-const o Float32)
(assert (forall ((V Float32))
  (fp.eq (ite x1 o (_ -oo 8 24))
         (ite x4 (_ NaN 8 24) (ite x41 (_ NaN 8 24) (ite x V (_ NaN 8 24)))))))
(assert (exists ((V Float32))
  (not (fp.eq (ite x4 (_ NaN 8 24) (ite x41 (_ NaN 8 24) (ite x V (_ NaN 8 24))))
              (ite x1 o (_ -oo 8 24))))))
(check-sat)
```

### CVC5#12306 — OR not commutative in BF16

**Bug**: CVC5 returns different results depending on the order of operands in
an OR for BF16 (`(_ FloatingPoint 8 8)`) formulas. Involves bound checking
with `fp.leq`/`fp.geq` and multiplication.

**Category**: Requires attached files for full reproducer. Core issue is
non-commutativity of disjunction in FP reasoning.

### CVC5#12383 — Performance slowdown on equivalent files

**Bug**: Semantically equivalent SMT2 files (one with explicit normalization
assertions) show significant performance difference. Same issue as Z3#8282.

**Category**: Performance — not a correctness issue.

### Bitwuzla#130 — SymFPU fp.div bug for non-standard FP format

**Bug**: Bitwuzla incorrectly returns `unsat` for a satisfiable QF_BVFP formula
involving `fp.div` with RNA rounding on `(_ FloatingPoint 4 12)` (non-standard
format). Z3 correctly returns `sat`.

**Reproducer** (large, involves many BV/FP conversions):
```smt2
(set-logic QF_BVFP)
; ... (large formula involving fp.div RNA on (_ FloatingPoint 4 12))
; ... and fp.to_sbv, to_fp, to_fp_unsigned with non-standard sorts
(check-sat)
```

---

## Categorization by FP Operation / Feature

| Category | Issues |
|----------|--------|
| **fp.sub / fp.add** | Z3#7162, Z3#4673 |
| **fp.fma** | Z3#7162, CVC5#11139 |
| **fp.div** | CVC5#11139, CVC5#12335, Bitwuzla#130 |
| **fp.rem** | Z3#2381, Z3#8414 |
| **fp.to_real / to_fp from Real** | Z3#7321, Z3#8169, Z3#8345, Z3#6633, Z3#6548, CVC5#12371 |
| **NaN handling** | Z3#6728, Z3#7842, CVC5#12387 |
| **fp.eq semantics** | Z3#7321, CVC5#12335, CVC5#12387 |
| **fp.roundToIntegral** | Z3#7056 |
| **Non-standard FP sorts** | Z3#8169, Z3#8414, Bitwuzla#130, CVC5#12306 |
| **Quantifiers + FP** | Z3#2631, Z3#2596, CVC5#12335, CVC5#12371, CVC5#12387 |
| **Incremental solving** | Z3#8345, Z3#6861 |
| **Uninterpreted functions + FP** | Z3#6728, Z3#8097 |
| **Performance** | Z3#6294, Z3#8282, CVC5#12383 |
| **Crashes / assertion violations** | Z3#5911, Z3#5284, Z3#6460, Z3#6464, Z3#6674, Z3#8097, Z3#8414, CVC5#11139, CVC5#12335, CVC5#12387 |

---

## Priority for CBMC Testing

The most relevant issues for CBMC are those involving:

1. **Core FP arithmetic** (add, sub, mul, div, fma, rem) — these directly map
   to C floating-point operations
2. **NaN handling** — C programs can produce NaN; CBMC must reason about it
3. **Rounding modes** — C has `fesetround()`; CBMC's encoding must handle all
   IEEE 754 rounding modes
4. **FP-to-integer and integer-to-FP conversions** — common in C code
5. **fp.to_real** — used internally in some CBMC encodings
6. **Non-standard FP sorts** — relevant if CBMC supports non-standard widths
   (e.g., `_Float16`, `__bf16`)

Lower priority:
- Quantifier-related issues (CBMC's own solver is quantifier-free)
- Datatype-related issues (Z3#7842 — CBMC doesn't use SMT datatypes for FP)
- Performance issues (Z3#8282, CVC5#12383)
- Incremental solving issues (Z3#8345 — CBMC doesn't use incremental mode)

---

## Progress Log

- **2026-03-20**: Created initial tracking document. Fetched and catalogued all
  55 issues from Z3 (Floats label), CVC5, and Bitwuzla. Extracted SMT-LIB
  reproducers from issue bodies. Categorized by FP operation/feature.
- **2026-03-20**: Created first batch of regression tests. Tested CBMC's SMT2
  solver capabilities. Found the following bugs/gaps:
  1. **fp.rem always returns +0.0** — CBMC's SMT2 solver `fp.rem` implementation
     appears to be broken, always returning positive zero regardless of inputs.
     Test: `regression/smt2_solver/fp-rem-nonstandard/fp-rem1.smt2` (KNOWNBUG)
  2. **remainderf/remainder crashes CBMC** — The C front-end crashes with an
     invariant violation in `numeric_cast_v` when processing `remainderf()` or
     `remainder()`. The crash involves a 128-bit floatbv constant.
     Test: `regression/cbmc/Float-rem1/` (KNOWNBUG)
  3. **fp.fma not supported in SMT2 solver** — The solver reports "unknown
     function symbol 'fp.fma'" and ignores the assertion, leading to incorrect
     results. Test: `regression/smt2_solver/fp/fp-fma-unsupported1.smt2`
  4. **fp.to_real not supported in SMT2 solver** — Same behavior as fp.fma.
     Test: `regression/smt2_solver/fp/fp-to-real-unsupported1.smt2`

  Tests passing correctly:
  - NaN equality through UFs (Z3#6728)
  - fp.sub with all rounding modes including RTN→-0 (Z3#7162)
  - fp.div with RTN and non-standard sorts (CVC5#11139, Bitwuzla#130)
  - fp.rem on non-standard sort doesn't crash (Z3#8414)
  - Overflow to infinity (Z3#4673)
  - NaN propagation in C (Z3#6728)
  - x - x == +0 with RNE in C (Z3#7162)
  - Float division edge cases in C (CVC5#11139, Bitwuzla#130)
  - fmaf correctness in C (Z3#7162, CVC5#11139)
  - Overflow to infinity in C (Z3#4673)
