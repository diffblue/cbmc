int main() {
  float a, b;
  __CPROVER_assume(!__CPROVER_isnanf(a) && !__CPROVER_isinff(a));
  __CPROVER_assume(!__CPROVER_isnanf(b) && !__CPROVER_isinff(b));
  __CPROVER_assume(a >= 0.0f && a <= 1.0f);
  __CPROVER_assume(b >= 0.0f && b <= 1.0f);
  // Product of two [0,1] floats is in [0,1] (UNSAT — should be true)
  __CPROVER_assert(a * b >= 0.0f && a * b <= 1.0f, "product bounded");
}
