int main() {
  float a;
  __CPROVER_assume(!__CPROVER_isnanf(a) && !__CPROVER_isinff(a));
  __CPROVER_assert(a * 1.0f == a, "FP mul identity");
}
