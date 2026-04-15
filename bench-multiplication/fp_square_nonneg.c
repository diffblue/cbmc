int main() {
  float a;
  __CPROVER_assume(!__CPROVER_isnanf(a) && !__CPROVER_isinff(a));
  // a*a >= 0 for all finite floats (UNSAT — should be true)
  __CPROVER_assert(a * a >= 0.0f, "square nonneg");
}
