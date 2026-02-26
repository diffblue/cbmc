# SAT/SMT Disagreement Analysis: Quantifier Instantiation Bug

- **Date:** 2026-02-26
- **CBMC:** 6.8.0 (`9774e37369`, branch `features/quantifiers-elimination`)

## Summary

The SAT backend produces spurious counterexamples for `forall` expressions
with variable (non-constant) bounds. The complete instantiation algorithm
fails to generate correct constraints when the quantifier bound is a symbolic
variable, causing `__CPROVER_assume(forall ...)` to be treated as vacuously
true. The SMT backend (Z3) handles these correctly via native quantifier
support.

## Standalone Minimal Reproducer (9 lines)

```c
// File: quant_var_bound_bug.c
// Bug:  cbmc quant_var_bound_bug.c        => VERIFICATION FAILED (spurious)
//       cbmc --smt2 quant_var_bound_bug.c => VERIFICATION SUCCESSFUL
unsigned nondet_unsigned(void);
int main() {
  int t[2];
  unsigned k = nondet_unsigned();
  __CPROVER_assume(k < 2);
  __CPROVER_assume(__CPROVER_forall { unsigned r; (r < k) ==> t[r] < 10 });
  __CPROVER_assume(k == 1);
  __CPROVER_assert(t[0] < 10, "");
}
```

**Expected:** The forall assumption with `k==1` constrains `t[0] < 10`.
The assertion should pass.

**Actual (SAT):** The SAT solver finds a counterexample where `t[0]` is
unconstrained (e.g., `t[0]=536870912`), violating the assertion. The forall
assumption is accepted but not enforced.

**Actual (SMT):** Correctly reports VERIFICATION SUCCESSFUL.

## Root Cause

The bug is in the complete instantiation algorithm in
`src/solvers/flattening/boolbv_quantifier.cpp`.

### How quantifier instantiation works

1. **Eager instantiation** (`eager_quantifier_instantiation`): Tries to find
   constant bounds `[lb, ub]` for the quantified variable and expand the
   forall into a conjunction. This fails when the bound is a variable (e.g.,
   `k`) because `get_quantifier_var_max` only recognizes constant expressions.

2. **Complete instantiation** (`instantiate_one_quantifier`): Fallback that
   uses the Ge & de Moura CAV 2009 approach. It:
   a. Finds index contexts in the quantifier body (array accesses using the
      bound variable)
   b. Collects ground index terms from the `bv_cache` (all expressions
      already converted to bitvectors)
   c. Computes an instantiation set via fixed-point

### Where it breaks

After SSA renaming, the array in the quantifier body becomes an **array
literal** (e.g., `{t#1[0], t#1[1]}`), while array accesses elsewhere in the
formula use **SSA symbol expressions** (e.g., `t#1`). The `arrays_match`
function in `collect_ground_indices` compares these by:
- SSA L1 object identifier (for `ssa_exprt`)
- Structural equality (fallback)

The array literal `{t#1[0], t#1[1]}` does not structurally match the SSA
symbol `t#1`, so `collect_ground_indices` returns an empty set. With no
ground indices, `compute_instantiation_set` returns an empty set, and the
forall is instantiated with zero terms — effectively becoming `true`.

When this happens in an `assume`, the assumption is vacuous. The SAT solver
accepts it without constraining anything, leading to spurious counterexamples.

### Why constant bounds work

When the bound is a constant (e.g., `k=1` assigned before the forall), the
eager instantiation succeeds: it expands `forall r in [0,1): t[r] < 10`
into `t[0] < 10` directly, bypassing the complete instantiation entirely.

### Why SMT works

The SMT backend passes the forall to Z3 as a native SMT-LIB `forall`
expression. Z3's quantifier handling (E-matching, MBQI) correctly
instantiates it regardless of whether the bound is constant or symbolic.

## Affected Proofs

### Both CaDiCaL and MiniSat (4 proofs)

| Proof | Repo |
|-------|------|
| poly_compress_du | mlkem-native |
| poly_compress_dv | mlkem-native |
| polyveck_make_hint | mldsa-native |
| polyveck_pointwise_poly_montgomery | mldsa-native |

### MiniSat-only (12 additional mldsa proofs)

polyveck_caddq, polyveck_decompose, polyveck_invntt_tomont, polyveck_ntt,
polyveck_power2round, polyveck_reduce, polyveck_shiftl, polyveck_sub,
polyveck_use_hint, polyvecl_ntt, and others.

All share the pattern: DFCC loop contracts with `forall` invariants where
the loop counter is the quantifier bound.

## Verification of the Diagnosis

```bash
# Constant bound: WORKS (eager instantiation succeeds)
# k=1 is known at the time the forall is processed
cat > const_bound.c << 'EOF'
int main() {
  int t[2];
  unsigned k = 1;
  __CPROVER_assume(__CPROVER_forall { unsigned r; (r < k) ==> t[r] < 10 });
  __CPROVER_assert(t[0] < 10, "");
}
EOF
cbmc const_bound.c  # => VERIFICATION SUCCESSFUL

# Variable bound: FAILS (complete instantiation produces empty set)
cat > var_bound.c << 'EOF'
unsigned nondet_unsigned(void);
int main() {
  int t[2];
  unsigned k = nondet_unsigned();
  __CPROVER_assume(k < 2);
  __CPROVER_assume(__CPROVER_forall { unsigned r; (r < k) ==> t[r] < 10 });
  __CPROVER_assume(k == 1);
  __CPROVER_assert(t[0] < 10, "");
}
EOF
cbmc var_bound.c       # => VERIFICATION FAILED (spurious)
cbmc --smt2 var_bound.c  # => VERIFICATION SUCCESSFUL
```

## Suggested Fix

The `arrays_match` function needs to handle the case where the quantifier
body's array is an array literal (after SSA) by matching it against the
corresponding SSA symbol. Alternatively, the SSA encoding could be modified
to preserve the array symbol in quantifier bodies rather than expanding it
to a literal.

A simpler workaround: when `collect_ground_indices` returns an empty set,
fall back to instantiating with all indices `0..size-1` for fixed-size
arrays. This would be sound (though potentially expensive for large arrays).

## Scope

This bug is specific to the `features/quantifiers-elimination` branch. On
`develop`, the fallback for uninstantiated quantifiers is `conversion_failed`,
which would cause CBMC to report an error rather than silently produce wrong
results. The complete instantiation code introduced by this branch is the
source of the unsoundness.
