# Plan: Remaining FP Issues

## Phase 1: After `tautschnig/cleanup/floatbv-mod-rem` Lands

These are blocked by the branch and become straightforward once it merges.

### 1.1 `fp.fma` in SMT2 parser (~30 min)

The branch adds the full back-end (`float_utilst::fma`, `boolbvt`, `smt2_conv`).
Only the parser entry is missing.

- Add to `smt2_parser.cpp` `expressions["fp.fma"]`: parse 4 operands
  (rm + 3 FP), construct `floatbv_fma_exprt(op[1], op[2], op[3], op[0])`
- Turn KNOWNBUG tests to CORE: `z3-6117-fma`, `z3-7162-fma`,
  `cvc5-11139-fma`, `fp-fma-unsupported1`

### 1.2 `fp.rem` KNOWNBUG→CORE (~15 min)

The branch fixes `float_utilst::rem()`. Just verify and flip:
- `z3-2381-rem-specific`, `z3-6553-rem`, `fp-rem1`

### 1.3 C front-end `fma` and `remainder` KNOWNBUG→CORE (~15 min)

The branch adds `__CPROVER_fma{,f,l}` and `__CPROVER_remainder{,f,l}`.
- `Float-fma-precision1`, `Float-rem1`

---

## Phase 2: Independent Fixes (no branch dependency)

### 2.1 Fix `fp.sqrt` rounding mode handling (~2-4 hours)

**Problem**: The current constraint `r*r_low <= x <= r*r_high` finds *a*
valid square root but doesn't enforce the correct rounding direction.

**Plan**:
1. After finding `r` via the bracketing constraint, also compute `r_next`
   (the next FP value above `r`) using an increment operation.
2. Add constraints that select between `r` and `r_next` based on the
   rounding mode:
   - RTZ/RTN: pick the smaller of `r`, `r_next` (the one whose square
     doesn't exceed `x`)
   - RTP: pick the larger (the one whose square is >= exact sqrt)
   - RNE: pick whichever `r` or `r_next` has `r*r` closer to `x`;
     on tie, pick the one with LSB=0
   - RNA: pick whichever is closer; on tie, pick the larger
3. This is essentially the same logic as the C library model but encoded
   at the SAT level.

**Files**: `src/solvers/floatbv/float_utils.cpp` (modify `sqrt()`)

**Tests**: Turn `fp-sqrt-rtz` KNOWNBUG→CORE.

### 2.2 Fix `fp.sqrt` subnormal handling (~1-2 hours)

**Problem**: For subnormal inputs, `r*r` may lose precision due to
subnormal arithmetic, making the bracketing constraint too loose.

**Plan**:
1. For subnormal inputs, the result is always normal (sqrt makes the
   exponent larger). The issue is that `r*r` with RTZ may underflow
   to a different subnormal than `x`.
2. Fix: widen the multiplication to double precision (similar to the
   `roundToIntegral` fix), compute `r*r` in the wider format, then
   compare with `x` widened to the same format.
3. Alternative: use the same approach as the C library — constrain
   `r >= 0 && r*r == x` directly for subnormals (since the C library
   comment says "all subnormals seem to be perfect squares" in FP
   arithmetic).

**Files**: `src/solvers/floatbv/float_utils.cpp` (modify `sqrt()`)

**Tests**: Turn `fp-sqrt-subnormal` KNOWNBUG→CORE.

### 2.3 Add `__CPROVER_sqrtf` built-in to C front-end (~2-3 hours)

**Problem**: `sqrtf`/`sqrt`/`sqrtl` use a `__VERIFIER_nondet` + assume
model that has known rounding and subnormal issues.

**Plan**:
1. Add `__CPROVER_sqrt{,f,l}` to `cprover_builtin_headers.h`
2. Add type-checking in `c_typecheck_expr.cpp` (same pattern as
   `__CPROVER_fmod`): construct a `floatbv_sqrt_exprt` or reuse
   `ieee_float_op_exprt` with `ID_floatbv_sqrt`
3. Add rounding mode insertion in `adjust_float_expressions.cpp`
4. Update `math.c` to use `__CPROVER_sqrtf(x)` instead of the
   nondet model
5. Add `ID_floatbv_sqrt` handling in `smt2_conv.cpp`: emit
   `(fp.sqrt RM x)` when using FPA theory
6. Add `ID_floatbv_sqrt` handling in `float_bv.cpp` for constant
   folding (or leave as TODO with a clear error)

**Files**: `src/ansi-c/cprover_builtin_headers.h`,
`src/ansi-c/c_typecheck_expr.cpp`, `src/ansi-c/library/math.c`,
`src/goto-programs/adjust_float_expressions.cpp`,
`src/solvers/smt2/smt2_conv.cpp`, `src/solvers/floatbv/float_bv.cpp`

**Tests**: Turn `Float-sqrt-rounding1` KNOWNBUG→CORE.

### 2.4 Add `__CPROVER_fmin`/`__CPROVER_fmax` built-ins (~2-3 hours)

**Problem**: `fmin`/`fmax` C library models use `(f <= g) ? f : g` which
doesn't handle the -0/+0 tie-breaking correctly.

**Plan**:
1. Add `__CPROVER_fmin{,f,l}` and `__CPROVER_fmax{,f,l}` to
   `cprover_builtin_headers.h`
2. Add new expression types `ID_floatbv_min`/`ID_floatbv_max` to
   `irep_ids.def`
3. Type-check in `c_typecheck_expr.cpp`
4. Handle in `boolbv.cpp` → dispatch to `float_utilst` (add `min()`
   and `max()` methods, or express as compound like the parser does)
5. Handle in `smt2_conv.cpp`: emit `(fp.min x y)` / `(fp.max x y)`
6. Update `math.c` to use the built-ins
7. Handle in `float_bv.cpp` for constant folding

**Files**: Same set as 2.3 plus `src/solvers/floatbv/float_utils.{h,cpp}`

**Tests**: Turn `Float-fmin-zero-sign1` KNOWNBUG→CORE.

---

## Phase 3: Larger Efforts

### 3.1 `fp.to_real` support (~1-2 days)

**Problem**: `fp.to_real` converts FP to exact rational. CBMC's solver
has no rational arithmetic.

**Plan (SMT2 output path only)**:
1. Add `ID_floatbv_to_real` to `irep_ids.def`
2. Parse `fp.to_real` in `smt2_parser.cpp`
3. In `smt2_conv.cpp`, emit `(fp.to_real x)` when using FPA theory
4. For the standalone SAT-based solver, report a clear error:
   `"fp.to_real requires an external SMT solver with Real arithmetic"`

This doesn't give full standalone solver support but unblocks CBMC users
who use `--smt2` with Z3/CVC5.

**Tests**: Turn `fp.to_real` KNOWNBUG tests to CORE (for the SMT2 output
path) or update them to test the error message (for standalone solver).

### 3.2 `to_fp` from non-constant Real (~1 hour)

**Problem**: `((_ to_fp 8 24) RNE x)` where `x` is a Real variable
(not a constant) is not supported.

**Plan**: Same approach as 3.1 — support in SMT2 output path only.
For the standalone solver, this would require Real→FP conversion which
needs rational arithmetic.

### 3.3 `to_fp` from large Real constant (~1 hour)

**Problem**: `((_ to_fp 8 24) RNE 1e40)` fails because the parser
tries to convert the real constant to FP but the conversion code
doesn't handle overflow to infinity.

**Plan**: In the `to_fp` parsing code in `smt2_parser.cpp`, after
calling `ieee_floatt::from_base10()`, check if the result is infinity
and allow it (currently it may error or produce wrong results).

### 3.4 Quantifier support for FP (~large, out of scope)

The 4 quantifier KNOWNBUG tests document a pre-existing limitation:
the standalone solver ignores quantifiers with a warning. Full quantifier
support would require quantifier instantiation or MBQI, which is a
major architectural change. These tests serve as documentation.

---

## Dependency Graph

```
Branch lands ──→ 1.1 fp.fma parser
              ──→ 1.2 fp.rem KNOWNBUG→CORE
              ──→ 1.3 C fma/remainder KNOWNBUG→CORE

Independent ──→ 2.1 fp.sqrt rounding ──→ 2.3 C sqrt built-in
            ──→ 2.2 fp.sqrt subnormal ─┘
            ──→ 2.4 C fmin/fmax built-in
            ──→ 3.3 to_fp large Real constant

Later ──→ 3.1 fp.to_real (SMT2 output path)
      ──→ 3.2 to_fp from Real variable
      ──→ 3.4 Quantifiers (out of scope)
```

## Effort Summary

| Phase | Items | Total Effort |
|-------|-------|-------------|
| Phase 1 (after branch) | 1.1, 1.2, 1.3 | ~1 hour |
| Phase 2 (independent) | 2.1, 2.2, 2.3, 2.4 | ~8-12 hours |
| Phase 3 (larger) | 3.1, 3.2, 3.3, 3.4 | ~2-3 days |
