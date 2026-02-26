# Invariant Violation Analysis: `--arrays-uf-always` with SAT Backend

- **Date:** 2026-02-26
- **CBMC:** 6.8.0 (`9774e37369`, branch `features/quantifiers-elimination`)
- **Affected proofs:** 3 mldsa-native proofs (invariant violation), plus any code
  using `--arrays-uf-always` with array-of-structs patterns

## Summary

CBMC crashes with invariant violations when using `--arrays-uf-always` with the
SAT backend on code that contains array-of-structs with array members. The SMT
backend is unaffected because it bypasses the arrays theory flattening code.

## Standalone Minimal Reproducer (6 lines)

```c
// File: arrays_uf_crash.c
// Crash: cbmc --arrays-uf-always arrays_uf_crash.c
// OK:   cbmc arrays_uf_crash.c
// OK:   cbmc --smt2 --arrays-uf-always arrays_uf_crash.c
struct S { int a[1]; };
int main() {
  struct S x[2];
  int i;
  __CPROVER_assume(i >= 0 && i < 2);
  __CPROVER_assert(x[i].a[0] == 0, "");
}
```

**Crash output:**
```
Invariant check failed
File: src/solvers/flattening/arrays.cpp:563 function: add_array_constraints
Condition: false
Reason: unexpected array expression (add_array_constraints): 'member'
```

## Original mldsa-native Reproducers

These crash at a different location (`arrays.cpp:198`, `collect_arrays`) but the
same root cause — `member` expressions not handled in the arrays theory:

```bash
# polyveck_add (object-bits 8)
cbmc --object-bits 8 --arrays-uf-always \
  proofs/cbmc/polyveck_add/gotos/polyveck_add_harness.goto

# polyvec_matrix_pointwise_montgomery (object-bits 8)
cbmc --object-bits 8 --arrays-uf-always \
  proofs/cbmc/polyvec_matrix_pointwise_montgomery/gotos/polyvec_matrix_pointwise_montgomery_harness.goto

# polyvec_matrix_expand_serial (object-bits 11)
cbmc --object-bits 11 --arrays-uf-always \
  proofs/cbmc/polyvec_matrix_expand_serial/gotos/polyvec_matrix_expand_harness.goto
```

**Crash output:**
```
Invariant check failed
File: src/solvers/flattening/arrays.cpp:198 function: collect_arrays
Condition: struct_op.id() == ID_symbol || struct_op.id() == ID_nondet_symbol
Reason: unexpected array expression: member with 'index'
```

## Root Cause

When `--arrays-uf-always` is set, `is_unbounded_array()` returns `true` for all
arrays (not just large ones). This routes all array operations through the
arrays theory code (`collect_arrays`, `add_array_constraints`), which doesn't
handle `member` expressions.

The expression pattern that triggers the crash is `member(index(arr, i), field)`
where `field` has array type — i.e., `arr[i].field` for an array-of-structs
where `field` is itself an array. Two code paths crash:

1. **`collect_arrays` (line 198):** Expects `member` expressions to have
   `symbol` or `nondet_symbol` as the struct operand. Crashes when the struct
   operand is an `index` expression.

2. **`add_array_constraints` (line 563):** Has no handler for `member`
   expressions at all — falls through to the `DATA_INVARIANT(false, ...)` catch-all.

The standalone reproducer hits path 2. The mldsa-native proofs hit path 1
because DFCC instrumentation creates a different expression structure.

## Trigger Conditions

- `--arrays-uf-always` flag (required)
- SAT backend (CaDiCaL or MiniSat)
- Code with array-of-structs where struct members are arrays
- Nondet index into the outer array

The crash does NOT occur:
- Without `--arrays-uf-always` (arrays are flattened instead)
- With `--smt2` (SMT backend bypasses the arrays theory code entirely)
- With constant indices only

## Scope

This is a pre-existing CBMC bug, not related to the quantifier elimination
branch. It affects `src/solvers/flattening/arrays.cpp` which has not been
modified by this branch.
