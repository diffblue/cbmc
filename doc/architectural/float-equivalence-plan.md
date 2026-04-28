# Plan: Automated Equivalence Checking of `float_utilst` vs `float_bvt`

## 1. Problem Statement

CBMC has two independent floating-point encodings:

- **`float_utilst`** — operates on `bvt` (vectors of SAT literals), used by the
  bit-blasting path (`boolbvt`). Takes bitvector arguments, produces bitvector
  results directly via a `propt` (SAT solver interface).
- **`float_bvt`** — operates on `exprt` (CBMC expression trees), used by the
  SMT path. Takes expression arguments, produces expression results that are
  later lowered to bitvectors or SMT.

Both implement the same IEEE 754 operations (add, sub, mul, div, fma,
conversions, relations, predicates, abs, negate). They should be semantically
identical: for any operation and any inputs, both encodings must describe
exactly the same set of satisfying assignments.

## 2. Approach: SAT-Based Equivalence Checking (Miter Construction)

The core idea is a **miter test**: for each operation, construct a formula that
asserts the two encodings produce *different* results for the *same* symbolic
inputs, then check unsatisfiability. If UNSAT, the encodings are equivalent. If
SAT, the model is a counterexample.

### Why this works

Both encodings ultimately produce constraints over bitvectors. `float_utilst`
produces them directly as SAT literals. `float_bvt` produces `exprt` trees that
can be bit-blasted through the existing `boolbvt` machinery. We can run both in
the same SAT instance, share the input literals, and add a "not-equal"
constraint on the outputs.

### Why not random testing

Random testing (like the existing unit test) gives confidence but cannot prove
equivalence — it only covers a finite sample. The miter approach is exhaustive
for a given bit-width. For single-precision (32-bit), the miter formula is large
but tractable for modern SAT solvers. For double-precision, we can use smaller
custom formats (e.g., 5-bit exponent, 4-bit fraction) to keep solve times
CI-friendly.

## 3. Prior Analysis

### `float_utilst` (src/solvers/floatbv/float_utils.h/.cpp)

- Operates on `bvt` (vectors of `literalt`), requires a `propt &` (SAT solver).
- Stores `ieee_float_spect spec` and `rounding_mode_bitst` as member state.
- Key methods: `add`, `sub`, `mul`, `div`, `fma`, `rem`, `abs`, `negate`,
  `from_signed_integer`, `from_unsigned_integer`, `to_signed_integer`,
  `to_unsigned_integer`, `conversion`, `round_to_integral`, `relation`,
  `is_NaN`, `is_zero`, `is_infinity`, `is_normal`, `is_plus_inf`,
  `is_minus_inf`.
- Used by `boolbvt` (the bit-blasting decision procedure) in files like
  `boolbv_floatbv_op.cpp`, `boolbv_typecast.cpp`, `boolbv_add_sub.cpp`,
  `boolbv_floatbv_fma.cpp`, `boolbv_floatbv_mod_rem.cpp`, etc.

### `float_bvt` (src/solvers/floatbv/float_bv.h/.cpp)

- Operates on `exprt`, stateless (methods are `const` or `static`).
- Key methods: `add_sub`, `mul`, `div`, `fma`, `abs`, `negation`, `is_equal`,
  `relation`, `isnan`, `isinf`, `isnormal`, `isfinite`, `is_zero`,
  `from_signed_integer`, `from_unsigned_integer`, `to_signed_integer`,
  `to_unsigned_integer`, `conversion`, `sign_bit`.
- `convert(const exprt &)` dispatches on expression ID to the appropriate
  method.
- Used by the SMT paths: `smt2_incremental_decision_procedure.cpp` (via
  `lower_floatbv`), `smt2_conv.cpp`.

### Existing tests

- `unit/solvers/floatbv/float_utils.cpp` tests `float_utilst` against native
  float arithmetic using random sampling (200 iterations of add/sub/mul/div).
  Also tests `round_to_integral` and `fma` with specific values.
- No existing equivalence tests between the two encodings.
- No unit tests for `float_bvt` at all.

## 4. Operations to Cover

### Common to both encodings (must test)

| Category | `float_utilst` method | `float_bvt` method |
|---|---|---|
| Addition | `add(a, b)` | `add_sub(false, a, b, rm, spec)` |
| Subtraction | `sub(a, b)` | `add_sub(true, a, b, rm, spec)` |
| Multiplication | `mul(a, b)` | `mul(a, b, rm, spec)` |
| Division | `div(a, b)` | `div(a, b, rm, spec)` |
| FMA | `fma(a, b, c)` | `fma(a, b, c, rm, spec)` |
| Abs | `abs(a)` | `abs(a, spec)` |
| Negate | `negate(a)` | `negation(a, spec)` |
| Is-equal | `relation(a, EQ, b)` | `is_equal(a, b, spec)` |
| Relations (LT/LE/GT/GE) | `relation(a, rel, b)` | `relation(a, rel, b, spec)` |
| Is-NaN | `is_NaN(a)` | `isnan(a, spec)` |
| Is-Inf | `is_infinity(a)` | `isinf(a, spec)` |
| Is-Normal | `is_normal(a)` | `isnormal(a, spec)` |
| Is-Zero | `is_zero(a)` | `is_zero(a)` |
| Float→signed int | `to_signed_integer(a, w)` | `to_signed_integer(a, w, rm, spec)` |
| Float→unsigned int | `to_unsigned_integer(a, w)` | `to_unsigned_integer(a, w, rm, spec)` |
| Signed int→float | `from_signed_integer(a)` | `from_signed_integer(a, rm, spec)` |
| Unsigned int→float | `from_unsigned_integer(a)` | `from_unsigned_integer(a, rm, spec)` |
| Float→float conversion | `conversion(a, dest_spec)` | `conversion(a, rm, src_spec, dest_spec)` |

### Only in `float_utilst` (no `float_bvt` counterpart)

- `rem(a, b)` — used by `boolbv_floatbv_mod_rem.cpp`
- `round_to_integral(a)` — used by `boolbv_floatbv_op.cpp`
- `is_plus_inf(a)`, `is_minus_inf(a)` — finer-grained predicates

### Only in `float_bvt` (no `float_utilst` counterpart)

- `isfinite(a, spec)` — trivially `!isnan && !isinf`

## 5. Test Architecture

### 5.1 File location

`unit/solvers/floatbv/float_bv_utils_equivalence.cpp`

### 5.2 Core mechanism

For each operation, the test:

1. Creates a single `satcheckt` instance.
2. Creates a `float_utilst` on that SAT instance with symbolic (unconstrained)
   inputs.
3. Allocates fresh SAT variables for each input operand (shared bitvectors).
4. Runs the `float_utilst` operation on those bitvectors → gets result bitvector
   `R_utils`.
5. Wraps the same input bitvectors as `exprt` symbols, constructs the
   corresponding `float_bvt` expression, then bit-blasts the `float_bvt` output
   through `boolbvt` → gets result bitvector `R_bv`.
6. Adds a constraint: `R_utils ≠ R_bv`.
7. Calls `prop_solve()`. Expects **UNSAT**.
8. If SAT: extracts the counterexample model and reports it.

### 5.3 Bridging `float_bvt` output back to SAT literals

The key technical challenge: `float_bvt` produces an `exprt`, but we need SAT
literals to compare against `float_utilst` output. The solution:

- Create a `boolbvt` instance on the same `satcheckt`.
- Register the input symbols in the `boolbvt`'s namespace, constrained to equal
  the same SAT variables used by `float_utilst`.
- Call `boolbvt::convert_bv()` on the `float_bvt` output expression. This
  bit-blasts the expression tree into the same SAT instance.
- Now both result bitvectors live in the same SAT instance and can be compared.

### 5.4 Handling rounding modes

Both encodings support symbolic rounding modes. The test should use a shared
symbolic rounding-mode bitvector, constrained to be one of the five valid
IEEE 754 modes. This ensures equivalence is checked across all rounding modes
simultaneously.

### 5.5 Floating-point formats to test

| Format | Exponent bits | Fraction bits | Total bits | Purpose |
|---|---|---|---|---|
| Tiny (custom) | 3 | 3 | 7 | Fast CI smoke test |
| Small (custom) | 4 | 5 | 10 | Matches IEEE half layout |
| Half precision | 5 | 10 | 16 | Standard format, still fast |
| Single precision | 8 | 23 | 32 | Full production, slower |

For CI, run tiny + small + half. Single precision as nightly/weekly.

### 5.6 Handling boolean vs bitvector results

Some operations return a `literalt` in `float_utilst` but an `exprt` in
`float_bvt`. For these (relations, predicates), the miter compares a single
literal against the bit-blasted boolean expression.

## 6. Implementation Plan

### Phase 1: Infrastructure (the test harness)

Helper functions:
- `make_symbolic_bv` — creates unconstrained bitvector in SAT solver
- `register_bv_as_symbol` — wraps bvt as symbol_exprt in boolbvt
- `constrain_rounding_mode` — restricts rm to valid IEEE modes
- `assert_not_equal` — the miter constraint

### Phase 2: Per-operation test cases

For each operation, a `TEST_CASE` parameterized over floating-point format.

### Phase 3: Conversion operations

Int↔float and float↔float with mixed-width inputs/outputs.

### Phase 4: CI integration

- Tag: `[core][solvers][floatbv][equivalence]`
- Tiny + small + half in CORE suite
- Single precision tagged `[.][thorough]`

### Phase 5: Coverage gap tracking

Stubs/comments for operations in only one encoding.

## 7. Execution Order

1. Write the harness infrastructure.
2. Implement simplest miter first: `abs` or `negate` (no rounding mode, unary).
3. Add binary arithmetic: `add`, `sub`, `mul`, `div`.
4. Add `fma` (ternary).
5. Add relations and predicates.
6. Add conversions (int↔float, float↔float).
7. Parameterize over formats.
8. Add CI tags and timeout guards.
9. Document coverage gaps.

## 8. Risks and Mitigations

| Risk | Mitigation |
|---|---|
| SAT blowup on larger formats | Tiny/small/half for CI; single as nightly. Use `timeout`. |
| `boolbvt` setup complexity | Follow existing patterns in `unit/solvers/`. |
| Intentional differences (e.g., `rem`) | Document; test only shared operations. |
| `float_bvt::convert` returns nil | Track as coverage gaps. |
| Rounding mode encoding differs | Shared symbolic RM constrained to valid values. |

## 9. Progress Log

### 2026-04-26: Initial implementation complete (Steps 1–7)

**Commits:**
- `02abcdda85` — Plan document
- `4ebfa62d75` — Equivalence test file with all shared operations

**Test file:** `unit/solvers/floatbv/float_bv_utils_equivalence.cpp`

**Infrastructure (Step 1):**
- `test_environt` struct encapsulates satcheckt + boolbvt + float_utilst with
  shared symbolic inputs (a, b, rm).
- `make_input()` creates a symbol, adds it to the symbol table, and obtains its
  SAT literals from boolbvt. Both encodings share the same SAT variables because
  boolbvt maps the symbol to literals, and float_utilst operates on those same
  literals.
- `constrain_rounding_mode()` restricts the symbolic rounding mode to 0..4.
- `miter_not_equal()` asserts two bitvectors differ.
- `check_unsat()` verifies UNSAT and prints counterexamples on SAT.

**Operations implemented (Steps 2–6):** All 18 operations from the table in
Section 4 are covered. The `to_signed/unsigned_integer` tests use a fixed
ROUND_TO_ZERO mode because `float_utilst::to_integer` has a hard precondition
requiring it.

**Formats (Step 7):** Three formats tested: tiny (e=3,f=3), small (e=4,f=5),
half precision (e=5,f=10). All tests complete in <30ms each.

### Findings: Equivalence Results

| Operation | Tiny (3,3) | Small (4,5) | Half (5,10) | Notes |
|---|---|---|---|---|
| abs | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| negate | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| relation LT | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| relation LE | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| relation GT | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| relation GE | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| relation EQ | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| is_equal | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| isnan | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| isinf | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| isnormal | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| is_zero | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT | Proven equivalent |
| add | ❌ SAT | ❌ SAT | ❌ SAT | rm=4 (ROUND_TO_AWAY) |
| sub | ❌ SAT | ❌ SAT | ❌ SAT | rm=4 |
| mul | ❌ SAT | ❌ SAT | ❌ SAT | rm=4 |
| div | ❌ SAT | ❌ SAT | ❌ SAT | rm=4 (also rm=2 at half) |
| fma | ❌ SAT | ❌ SAT | ❌ SAT | rm=1,3,4 seen |
| from_signed_int | ✅ UNSAT | ❌ SAT | ❌ SAT | rm=4 |
| from_unsigned_int | ✅ UNSAT | ❌ SAT | ❌ SAT | rm=4 |
| to_signed_int | ✅ UNSAT | ❌ SAT | ❌ SAT | Fixed rm=0 |
| to_unsigned_int | ✅ UNSAT | ❌ SAT | ❌ SAT | Fixed rm=0 |
| float→float conv | N/A | ❌ SAT | ❌ SAT | rm=4 |

**18 test cases total: 8 pass, 10 fail.**

### Analysis of Counterexamples

**Dominant pattern:** Nearly all arithmetic/conversion failures involve rounding
mode 4 (ROUND_TO_AWAY). Manual verification of the first counterexample
(`-4 + 0.15625 = -3.84375` in tiny format) confirms `float_bvt` produces the
correct IEEE 754 result (`-4`, rounding away from zero) while `float_utilst`
produces `-3.75` (incorrect).

**Division outlier:** The half-precision div test found a violation at rm=2
(ROUND_TO_PLUS_INF), suggesting a broader rounding issue in `float_utilst`
beyond just ROUND_TO_AWAY.

**FMA:** Violations seen at rm=1 (ROUND_TO_ZERO), rm=3 (ROUND_TO_MINUS_INF),
and rm=4 (ROUND_TO_AWAY), indicating more pervasive rounding differences in the
FMA implementation.

**Conversion failures at larger formats:** `from_signed/unsigned_integer` pass
at tiny (e=3,f=3) but fail at larger formats. This may indicate the bug only
manifests when the integer value requires rounding to fit the float format.

**to_signed/unsigned_integer failures:** These use a fixed ROUND_TO_ZERO mode
(required by `float_utilst` precondition), yet still fail at larger formats.
This suggests a non-rounding-related difference in the integer conversion logic.

### Remaining Steps

- ~~**Step 8:** Add single-precision tests tagged `[.][thorough]` for nightly.~~
  Done in commit `dbedeb440c`.
- ~~**Step 9:** Coverage gaps are documented as comments in the test file.~~
  Done.

### 2026-04-26: Steps 8–9 complete

**Commit:** `dbedeb440c` — Refactored test file with thorough tests

**Step 8 — Single-precision thorough tests:**
- Extracted all test bodies into reusable `static void test_*(spec)` functions.
- Added 18 parallel `TEST_CASE`s tagged
  `[.][thorough][solvers][floatbv][equivalence]`.
- The `[.]` tag hides them from default runs and from `[core]` selection.
- Run explicitly with: `build/bin/unit "[thorough]"`
- Single-precision tests complete in <250ms each (max observed: 236ms for div).
- Results mirror CORE: same 8 pass / 10 fail pattern.

**Step 9 — Coverage gaps:**
- Documented at the bottom of the test file as comments.
- `float_utilst`-only: `rem()`, `round_to_integral()`, `is_plus_inf()`,
  `is_minus_inf()`
- `float_bvt`-only: `isfinite()`

### All planned steps complete

| Step | Description | Status |
|---|---|---|
| 1 | Harness infrastructure | ✅ Done |
| 2 | Unary ops (abs, negate) | ✅ Done — proven equivalent |
| 3 | Binary arithmetic (add, sub, mul, div) | ✅ Done — violations found |
| 4 | FMA (ternary) | ✅ Done — violations found |
| 5 | Relations and predicates | ✅ Done — proven equivalent |
| 6 | Conversions (int↔float, float↔float) | ✅ Done — violations found |
| 7 | Parameterize over formats | ✅ Done — 3 CORE + 1 thorough |
| 8 | CI tags and thorough tests | ✅ Done |
| 9 | Document coverage gaps | ✅ Done |

### 2026-04-26: ROUND_TO_AWAY fix in float_bvt

**Commits:**
- `ce0242eb67` — Regression test for ROUND_TO_AWAY bug
- `05531d3c4f` — Fix: `fraction_rounding_decision` in float_bvt

**Root cause:** `float_bvt::fraction_rounding_decision` used
`or_exprt(rounding_bit, sticky_bit)` for ROUND_TO_AWAY. The correct formula
is just `rounding_bit`, matching `float_utilst`. The OR with sticky_bit caused
rounding away from zero even when the value was closer to the truncated result.

**Initial analysis was wrong:** The first counterexample (`-4 + 0.15625` in
tiny format) was initially interpreted as `float_utilst` being wrong. Detailed
analysis of the bit representations revealed `float_utilst` was correct and
`float_bvt` was wrong.

**Regression test:** `regression/cbmc/Float-round-to-away/` with both
`--floatbv` (bit-blasting) and `--smt2 --z3` (float_bvt) test descriptors.
The test uses `__CPROVER_assume` to constrain non-deterministic inputs to
specific values that trigger the bug.

**Equivalence results after fix:**

| Operation | Before fix | After fix |
|---|---|---|
| abs | ✅ | ✅ |
| negate | ✅ | ✅ |
| add | ❌ | ✅ Fixed |
| sub | ❌ | ✅ Fixed |
| mul | ❌ | ❌ Different bug |
| div | ❌ | ❌ Different bug |
| fma | ❌ | ❌ Different bug |
| relations (all) | ✅ | ✅ |
| predicates (all) | ✅ | ✅ |
| from_signed_int | ❌ | ✅ Fixed |
| from_unsigned_int | ❌ | ✅ Fixed |
| to_signed_int | ❌ | ❌ Different bug |
| to_unsigned_int | ❌ | ❌ Different bug |
| float→float conv | ❌ | ✅ Fixed |

**Remaining failures (5):** mul, div, fma, to_signed_int, to_unsigned_int.
These involve different rounding modes (rm=1 ROUND_TO_MINUS_INF, rm=2
ROUND_TO_PLUS_INF) and overflow/edge cases, not the ROUND_TO_AWAY bug.

### 2026-04-26: Fix remaining equivalence failures

**Commit:** `1f672a1791` — Fix remaining float_bvt equivalence failures

**Bugs found and fixed:**

1. **Division exponent overflow** (`float_bv.cpp`): Exponent extended by only
   1 bit (`spec.e+1`) instead of 2 (`spec.e+2`). Caused exponent wraparound
   for large quotients, producing garbage instead of infinity.

2. **FMA sign handling** (`float_bv.cpp`): Sign was always set to the add/sub
   sign, ignoring infinity and zero special cases. Added proper sign selection
   matching `float_utilst`.

3. **Overflow-to-infinity missing ROUND_TO_AWAY** (both files): `round_exponent`
   did not include `round_to_away` in the `overflow_to_inf` condition. Since
   ROUND_TO_AWAY is a round-to-nearest mode, overflow should produce infinity.

4. **Float-to-integer conversion** (`float_bv.cpp`): `to_integer` did not
   extend the fraction to `dest_width` before shifting, causing incorrect
   results when `dest_width > fraction_width`.

**Test spec adjustment:** Replaced half precision (e=5, f=10) with two smaller
formats (e=3,f=3 and e=4,f=5) in CORE specs. The mul/div/fma miters at half
precision exceed SAT solver time limits (~15+ minutes) but are proven equivalent
at the smaller formats. Half precision remains in the thorough suite.

**Final equivalence results:**

| Operation | CORE (7-bit, 10-bit) | Thorough (32-bit) |
|---|---|---|
| abs | ✅ UNSAT | ✅ UNSAT |
| negate | ✅ UNSAT | ✅ UNSAT |
| add | ✅ UNSAT | ✅ UNSAT |
| sub | ✅ UNSAT | ✅ UNSAT |
| mul | ✅ UNSAT | timeout |
| div | ✅ UNSAT | timeout |
| fma | ✅ UNSAT | timeout |
| relations (all) | ✅ UNSAT | ✅ UNSAT |
| predicates (all) | ✅ UNSAT | ✅ UNSAT |
| from_signed_int | ✅ UNSAT | ✅ UNSAT |
| from_unsigned_int | ✅ UNSAT | ✅ UNSAT |
| to_signed_int | ✅ UNSAT | ✅ UNSAT |
| to_unsigned_int | ✅ UNSAT | ✅ UNSAT |
| float→float conv | ✅ UNSAT | ✅ UNSAT |

**All 18 CORE tests pass. 68 assertions. ~24 seconds total.**

### 2026-04-27: Steps 5, 1, 3, 4 complete

**Commits:**
- `3bd163fa1d` — Regression tests for division overflow, FMA sign, float-to-int
- `66c2b21b8e` — Close coverage gaps: is_finite, round_to_integral
- `93fc61d786` — Extend random tests to all rounding modes

**Step 5 — Full regression suite:** All 44 Float* regression tests pass
(1 pre-existing THOROUGH test skipped).

**Step 1 — Regression tests for other fixes:** Three new test directories
added, each with both `--floatbv` and `--smt2` descriptors:
- `Float-div-overflow`: FLT_MAX / 0.5f under directed rounding modes
- `Float-fma-sign`: FMA with infinity inputs, sign correctness
- `Float-to-int-wide`: Float-to-int for values needing >24 bits

**Step 3 — Coverage gaps closed:**
- `float_utilst::is_finite()` added (matches `float_bvt::isfinite`)
- `float_bvt::round_to_integral()` added (matches `float_utilst`)
- `float_bvt::convert()` now handles `ID_floatbv_round_to_integral`
- Equivalence tests added for both (CORE + thorough)
- 20 CORE equivalence tests now (was 18), all pass
- Remaining gaps: `rem()`, `is_plus_inf()`, `is_minus_inf()` (float_utilst only)

**Step 4 — Random tests extended:**
- `float_utils_all_rounding_modes`: 5 modes x 100 iterations x 4 ops
- `float_utils_conversions_all_rounding_modes`: 5 modes x 50 iterations
- All pass, confirming float_utilst matches ieee_floatt across all modes

**Final test counts:**
- 20 CORE equivalence tests, 74 assertions
- 5 float_utils unit tests, 2914 assertions
- 53 regression test descriptors (Float*), all pass

### 2026-04-27: Steps 2, 6, 3, 5

**Step 2 — Full regression suite:** All CBMC, cbmc-library, and smt2_solver
regression tests pass. No regressions from any changes.

**Step 6 — SMT round_to_integral performance:** Attempted a direct bitvector
approach (mask-and-round per exponent value) to replace the add-magic-subtract-
magic algorithm. The approach had correctness issues with edge cases and was
reverted. The add-magic implementation is proven equivalent via the miter test
and works correctly for bit-blasting. The SMT non-FPA path remains a known
limitation (expression tree too large for Z3).

**Step 3 — Subnormal division fix:** Found and fixed a precision loss bug in
both `float_utilst::div` and `float_bvt::div`. When dividing a subnormal by a
normal, the subnormal's fraction has leading zeros (no hidden bit), causing the
division quotient to have fewer significant bits than needed. Fix: increase
`div_width` by `spec.f` extra bits to compensate. The random test now passes
consistently (was flaky before).

**Step 5 — CaDiCaL for larger miters:** Built with CaDiCaL SAT solver.
Results at single precision (e=8, f=23):
- mul: 131s ✅ proven equivalent (MiniSat couldn't even do half precision)
- add: 4.2s ✅
- sub: 3.9s ✅
- div: timeout (>20 min) ❌
- fma: timeout (>10 min) ❌
- abs, negate, relations, predicates, conversions: all pass quickly ✅

CaDiCaL dramatically improves scalability for multiplication but division
and FMA remain intractable at single precision.

### 2026-04-27: mod/rem rewrite, round_to_integral direct approach, infinity fix

**Commits:**
- `70ecf7547b` — Rewrite float_bvt::mod/rem with integer significand arithmetic
- `87006a805e` — Rewrite float_bvt::round_to_integral with direct bitvector approach
- `244c88c176` — Fix float_utilst::round_to_integral overflow for large values
- `006cd95bf5` — Fix float_utilst::rem infinity bug, fix float_bvt::rem type issues

**mod/rem rewrite:** Replaced the floating-point div/trunc/mul/sub approach in
`float_bvt::mod()` and `float_bvt::rem()` with exact integer significand
arithmetic matching `float_utilst::rem()`. The old approach introduced rounding
errors for large quotients. Also added proper special case handling (NaN
propagation via input NaN, infinity, zero) and sign preservation for fmod.
Used `extractbits_exprt` instead of `typecast_exprt` for bitwise
reinterpretation between `unsignedbv_typet` and `floatbv_typet` (the typecast
was misinterpreted as a value conversion by `smt2_conv`). The IEEE remainder
correction step uses integer-domain comparison (`2*r_int` vs `my_aligned`) and
`add_sub` instead of float-domain operations, avoiding huge expression trees.

**round_to_integral direct approach:** Replaced the add-magic-subtract-magic
algorithm in both `float_bvt` and `float_utilst` with a direct bitvector
approach that masks off fractional bits based on the exponent. For each possible
biased exponent value, computes a mask and rounding increment on the packed
representation. O(f) if-then-else branches, each simple. Advantages:
- Works with SMT non-FPA path (Z3 can handle the expression tree)
- Correctly handles values where |x| + 2^f would overflow
- The SMT regression test is promoted from KNOWNBUG to CORE

**float_utilst::rem infinity fix:** Guarded the IEEE remainder correction step
with `!special` so it's skipped for NaN/infinity/zero inputs. Previously,
`fma(±1, inf, fmod_result)` produced ±inf, overriding the correct result.

**Subnormal division:** Confirmed fully fixed — 20 consecutive random test
runs pass with no flakiness.

**Final test counts:**
- 24 CORE equivalence tests, 82 assertions, all pass
- 5 float_utils unit tests, 2914 assertions, all pass (20/20 runs stable)
- Full CBMC + cbmc-library regression suites pass

**Bugs found and fixed (total: 8):**
1. ROUND_TO_AWAY rounding decision in float_bvt (fraction_rounding_decision)
2. Division exponent overflow in float_bvt (spec.e+1 → spec.e+2)
3. FMA sign handling in float_bvt (missing infinity/zero sign logic)
4. Overflow-to-infinity missing ROUND_TO_AWAY (both encodings)
5. Float-to-integer conversion width in float_bvt (fraction not extended)
6. Subnormal division precision loss (both encodings, div_width too small)
7. round_to_integral overflow for large values (both encodings, add-magic)
8. IEEE remainder infinity bug in float_utilst (correction step not guarded)
