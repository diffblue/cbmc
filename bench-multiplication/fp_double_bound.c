int main() {
  double a, b;
  __CPROVER_assume(!__CPROVER_isnand(a) && !__CPROVER_isinfd(a));
  __CPROVER_assume(!__CPROVER_isnand(b) && !__CPROVER_isinfd(b));
  __CPROVER_assume(a >= 0.0 && a <= 1.0);
  __CPROVER_assume(b >= 0.0 && b <= 1.0);
  __CPROVER_assert(a * b <= 1.0, "double product bounded");
}
