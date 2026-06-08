int main() {
  float a, b;
  __CPROVER_assume(!__CPROVER_isnanf(a) && !__CPROVER_isinff(a));
  __CPROVER_assume(!__CPROVER_isnanf(b) && !__CPROVER_isinff(b));
  __CPROVER_assert(a * b == b * a, "FP mul commutativity");
}
