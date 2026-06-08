int main() {
  double a, b;
  __CPROVER_assume(!__CPROVER_isnand(a) && !__CPROVER_isinfd(a));
  __CPROVER_assume(!__CPROVER_isnand(b) && !__CPROVER_isinfd(b));
  double p1 = a * b;
  double p2 = b * a;
  __CPROVER_assert(p1 == p2, "double mul comm");
}
