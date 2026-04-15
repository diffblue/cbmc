int main() {
  float a, b, c;
  __CPROVER_assume(!__CPROVER_isnanf(a) && !__CPROVER_isinff(a));
  __CPROVER_assume(!__CPROVER_isnanf(b) && !__CPROVER_isinff(b));
  __CPROVER_assume(!__CPROVER_isnanf(c) && !__CPROVER_isinff(c));
  __CPROVER_assert((a * b) * c == a * (b * c), "FP mul associativity");
}
