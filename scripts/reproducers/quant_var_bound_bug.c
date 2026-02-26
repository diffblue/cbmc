// Minimal reproducer: SAT/SMT disagreement on forall with variable bound
//
// Bug:  cbmc quant_var_bound_bug.c        => VERIFICATION FAILED (spurious)
//       cbmc --smt2 quant_var_bound_bug.c => VERIFICATION SUCCESSFUL
//
// The SAT quantifier instantiation fails to generate constraints for
// forall expressions with variable (non-constant) bounds. The assume
// is accepted but not enforced, leading to spurious counterexamples.
unsigned nondet_unsigned(void);
int main() {
  int t[2];
  unsigned k = nondet_unsigned();
  __CPROVER_assume(k < 2);
  __CPROVER_assume(__CPROVER_forall { unsigned r; (r < k) ==> t[r] < 10 });
  __CPROVER_assume(k == 1);
  __CPROVER_assert(t[0] < 10, "should hold: forall with k==1 implies t[0]<10");
}
