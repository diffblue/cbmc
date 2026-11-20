# FP Implementation Analysis: Effort Estimates and Design Sketches

## Branch `tautschnig/cleanup/floatbv-mod-rem` Status

This branch (actively being worked on) addresses several of the gaps/bugs
found in our analysis. Here's what it covers:

### Already Implemented on the Branch

1. **FMA (`fp.fma`)** — Full implementation
   - New `floatbv_fma_exprt` expression type (`ID_floatbv_fma`)
   - `float_utilst::fma()` — bit-level implementation using exact
     double-width multiplication followed by aligned addition and single
     rounding
   - `boolbvt::convert_floatbv_fma()` — SAT encoding
   - `smt2_convt::convert_floatbv_fma()` — SMT2 output (emits `fp.fma`)
   - `__CPROVER_fma`/`fmaf`/`fmal` built-ins in C library
   - C type-checking in `c_typecheck_expr.cpp`
   - **NOT yet added**: SMT2 solver parser (`smt2_parser.cpp`) — the
     standalone `smt2_solver` binary still won't parse `fp.fma`

2. **`fp.rem` (IEEE remainder) fix** — Complete rewrite
   - Old code was a stub: `sub(src1, mul(div(src1, src2), src2))` which
     always returned +0.0 due to the round-trip cancellation
   - New algorithm: `q = div(x,y)`, `n = round_to_integral(q)`,
     `r = fma(-n, y, x)`, then try `n±1` and pick smallest `|r|`
   - Includes a Coq proof (`doc/proofs/fma_remainder.v`) for soundness
   - Both `float_utilst::rem()` and `float_bvt::rem()` updated

3. **`fmod` vs `remainder` distinction** — New `ID_floatbv_mod`
   - `fmod` uses round-to-zero (simpler, no FMA needed)
   - `remainder` uses round-to-even + FMA-based correction
   - `boolbv_floatbv_mod_rem.cpp` now sets correct rounding mode per op
   - C library uses `__CPROVER_fmod` and `__CPROVER_remainder` built-ins
     (removes the old `__sort_of_CPROVER_remainder` hack)

4. **`remainderf`/`remainder` crash fix** — Fixed
   - The old code went through `__sort_of_CPROVER_remainder` which used
     `long double` intermediate, causing the 128-bit floatbv invariant
     violation. The new code uses `__CPROVER_remainder` built-in directly.

### NOT Addressed by the Branch

The branch does NOT address:
- `fp.to_real`
- `fp.sqrt`
- `fp.min` / `fp.max`
- `fp.isSubnormal` / `fp.isNegative` / `fp.isPositive`
- `to_fp` from bitvector (reinterpret cast)
- `fp.to_sbv` / `fp.to_ubv` crash with non-RTZ rounding modes
- `fp.roundToIntegral` bug on non-standard FP sorts
- SMT2 solver parser support for `fp.fma`

---

## Effort Estimates for Remaining Gaps

### 1. `fp.fma` in SMT2 Solver Parser — **Small (1–2 hours)**

The branch already has the full back-end implementation. The only missing
piece is parsing `fp.fma` in `smt2_parser.cpp`.

**Sketch**: Add to the `expressions` map in `smt2_parser.cpp`:
```cpp
expressions["fp.fma"] = [this] {
  auto op = operands();
  if(op.size() != 4)
    throw error() << "fp.fma takes four operands";
  // op[0] = rounding mode, op[1..3] = FP operands
  return floatbv_fma_exprt(op[1], op[2], op[3], op[0]);
};
```

### 2. `fp.isSubnormal` — **Trivial (30 min)**

Already have `fp.isNormal`, `fp.isZero`, `fp.isNaN`, `fp.isInfinite`.
The predicate is: exponent is all-zeros AND mantissa is non-zero.

**Sketch**: Add to `smt2_parser.cpp` expressions map, create
`isnormal_exprt`-like expression, or directly construct:
```cpp
expressions["fp.isSubnormal"] = [this] {
  auto op = operands();
  // subnormal = !isNaN && !isInfinite && !isZero && !isNormal
  // Or directly: exponent == 0 && fraction != 0
  // Use existing infrastructure from float_utils
};
```
In `float_utils`, subnormal detection is already part of `unpack()`.
The `boolbv` layer already handles `ID_isnormal`; adding `ID_issubnormal`
follows the same pattern.

### 3. `fp.isNegative` / `fp.isPositive` — **Trivial (30 min each)**

These are just sign-bit checks combined with "not NaN".

**Sketch**:
- `fp.isNegative(x)` = `sign_bit(x) == 1 && !isNaN(x)`
- `fp.isPositive(x)` = `sign_bit(x) == 0 && !isNaN(x)`

The sign bit is the MSB of the bitvector representation. This is a
one-liner in the parser + a simple expression construction.

### 4. `fp.min` / `fp.max` — **Small-Medium (2–4 hours)**

IEEE 754-2019 semantics:
- `min(x, y)`: return the smaller; if equal, return the one with negative
  sign bit; if either is NaN, return the other (or NaN if both NaN)
- `max(x, y)`: symmetric

The tricky part is the NaN handling and the `-0 < +0` tie-breaking
(which differs from `fp.lt` where `-0 == +0`).

**Sketch**:
1. Add `ID_floatbv_min` / `ID_floatbv_max` expression types
2. In `float_utilst`, implement using existing `relation()` and
   `is_NaN()`:
   ```
   min(a, b) =
     if isNaN(a) then b
     else if isNaN(b) then a
     else if a < b then a
     else if b < a then b
     else if sign(a) then a  // -0 < +0
     else b
   ```
3. Add parser entries, boolbv conversion, smt2 output

### 5. `fp.sqrt` — **Medium-Large (1–3 days)**

Square root is significantly more complex than other operations. The
standard approach is Newton-Raphson iteration or digit-by-digit
computation, but in a SAT/SMT context, the typical approach is:

**Approach A — Existential encoding**: Assert `result * result == x`
(with appropriate rounding). This is what most bit-blasting solvers do.
Specifically: `sqrt(x) = r` iff `r >= 0 && r*r rounded == x` with
appropriate handling of rounding modes, NaN, infinity, and negative
inputs.

**Approach B — Direct bit-level algorithm**: Implement the restoring or
non-restoring square root algorithm at the bit level, similar to how
division is implemented.

**Sketch** (Approach A):
1. Introduce `result` as a fresh FP variable
2. Assert: `result >= 0`, `!isNaN(result)` (unless input is NaN/negative)
3. Assert: `mul(result, result) == x` with appropriate rounding
4. Handle special cases: `sqrt(NaN) = NaN`, `sqrt(+inf) = +inf`,
   `sqrt(-0) = -0`, `sqrt(negative) = NaN`

This is conceptually simple but may produce large SAT instances because
the multiplication constraint is quadratic in the bit-width.

**Approach B** would follow the pattern of `float_utilst::div()` but
with a square root algorithm. This is more work but produces tighter
encodings.

CBMC's C front-end already handles `sqrtf`/`sqrt` via the library model,
which uses `__CPROVER_sqrtf` etc. The back-end encoding is the missing
piece.

### 6. `to_fp` from BitVec (reinterpret cast) — **Small (1–2 hours)**

The SMT-LIB spec says `((_ to_fp eb sb) (_ BitVec m))` (with NO rounding
mode) is a reinterpret cast where `m = 1 + eb + (sb - 1)`.

The parser currently always expects a rounding mode as the first operand.
The fix is to check whether the first operand is a bitvector (not a
rounding mode) and handle the 1-argument case.

**Sketch**: In the `to_fp` parsing code in `smt2_parser.cpp`:
```cpp
// After parsing rounding_mode and source_op:
// Check if "rounding_mode" is actually a BitVec (reinterpret cast)
if(rounding_mode.type().id() == ID_unsignedbv &&
   to_unsignedbv_type(rounding_mode.type()).get_width() ==
     width_e + width_f)
{
  // This is the reinterpret cast: ((_ to_fp eb sb) BitVec)
  // The "rounding_mode" is actually the bitvector operand
  return typecast_exprt(rounding_mode, spec.to_type());
}
```

Actually, the cleaner approach is to parse the first operand, check its
type, and branch:
- If it's a rounding mode → parse second operand (existing code)
- If it's a bitvector of matching width → reinterpret cast

### 7. `fp.to_sbv` / `fp.to_ubv` crash fix — **Small (1–2 hours)**

The parser correctly constructs `floatbv_typecast_exprt`, but the
`float_utilst::to_integer()` function has a precondition requiring
`round_to_zero`. The fix is to either:

(a) Support all rounding modes in `to_integer()` — this requires
    implementing the rounding logic for integer conversion, or

(b) In the parser/lowering, convert the rounding mode: first round the
    FP value to integral using `fp.roundToIntegral` with the given
    rounding mode, then convert to integer with RTZ.

**Sketch** (approach b, simpler):
```
fp.to_sbv(rm, x) = to_sbv(RTZ, roundToIntegral(rm, x))
```
This is semantically correct and reuses existing infrastructure.

### 8. `fp.to_real` — **Medium (2–4 hours for basic support)**

`fp.to_real` converts a floating-point value to an exact real number.
This is fundamentally different from the other operations because it
crosses the FP/Real theory boundary.

For CBMC's own SAT-based solver, this would require introducing real
arithmetic support, which is a much larger undertaking. However, for the
SMT2 output path (when using an external solver), it's just a matter of
emitting `fp.to_real`.

**For the standalone SMT2 solver**: This would require either:
- Implementing rational arithmetic in the solver (major effort), or
- Encoding the real value as a sufficiently wide fixed-point or
  integer representation (feasible but lossy for large exponents)

**Practical approach**: For the SMT2 output converter, just emit
`fp.to_real`. For the standalone solver, report "unsupported" cleanly
rather than silently ignoring.

### 9. `fp.roundToIntegral` on non-standard sorts — **Small (1–2 hours)**

**Root cause**: The "magic number" approach uses `2^f` where `f` is the
number of fraction bits. For sorts where `2^f` exceeds the maximum
representable value (i.e., when `f >= 2^(e-1)`), the magic number is
always >= |x|, so the function returns the input unchanged.

**Fix**: Before the magic-number trick, check if the exponent is large
enough that the value is already integral. The condition is:
`actual_exponent >= f` (the value has no fractional bits). If the
exponent is smaller, use the magic-number trick but clamp the magic
number to the representable range.

Alternative fix: Use a different algorithm for small formats. Instead of
the magic-number trick, directly compute:
1. Extract the integer part by shifting
2. Round according to the rounding mode
3. Reconstruct the FP value

This is more complex but works for all formats.

**Simplest fix**: Add a guard: if `spec.f >= (1 << (spec.e - 1))`, fall
back to a direct implementation. For standard formats (Float16, Float32,
Float64, Float128), the magic-number approach always works because
`f < 2^(e-1)`.

---

## Summary Table

| Feature | Branch Status | Effort | Priority |
|---------|--------------|--------|----------|
| `fp.fma` (back-end) | ✅ Done | — | — |
| `fp.fma` (SMT2 parser) | ❌ Missing | Small (1–2h) | High |
| `fp.rem` fix | ✅ Done | — | — |
| `fmod` vs `remainder` | ✅ Done | — | — |
| `remainderf` crash | ✅ Done | — | — |
| `fp.isSubnormal` | ❌ Missing | Trivial (30min) | Medium |
| `fp.isNegative` | ❌ Missing | Trivial (30min) | Medium |
| `fp.isPositive` | ❌ Missing | Trivial (30min) | Medium |
| `fp.min` / `fp.max` | ❌ Missing | Small-Med (2–4h) | Medium |
| `fp.sqrt` | ❌ Missing | Med-Large (1–3d) | Low |
| `to_fp` from BV | ❌ Missing | Small (1–2h) | High |
| `fp.to_sbv`/`fp.to_ubv` crash | ❌ Missing | Small (1–2h) | High |
| `fp.to_real` | ❌ Missing | Medium (2–4h basic) | Low |
| `roundToIntegral` non-std sorts | ❌ Missing | Small (1–2h) | Medium |

### Total Remaining Effort (excluding branch work)

- **Quick wins** (< 2h each): `fp.fma` parser, `fp.isSubnormal`,
  `fp.isNegative`, `fp.isPositive`, `to_fp` from BV,
  `fp.to_sbv`/`fp.to_ubv` crash fix, `roundToIntegral` fix
  → ~8–12 hours total

- **Medium effort**: `fp.min`/`fp.max`, `fp.to_real` (basic)
  → ~4–8 hours total

- **Larger effort**: `fp.sqrt`
  → 1–3 days

### Additional Bug Found During Analysis

7. **`fp.to_sbv`/`fp.to_ubv` crash** — The parser correctly handles
   these indexed operators, but the solver crashes with an invariant
   violation when the rounding mode is not RTZ. The `to_integer()`
   function in `float_utils.cpp:92` has a hard precondition
   `rounding_mode_bits.round_to_zero.is_true()`.
