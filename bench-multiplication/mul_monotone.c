// Multiplication monotonicity: if a <= b and c > 0, then a*c <= b*c
// (for unsigned, this is true when no overflow)
#ifndef BW
#define BW 8
#endif
int main() {
  unsigned __CPROVER_bitvector[BW] a, b, c;
  __CPROVER_assume(a <= b);
  __CPROVER_assume(c > 0);
  // Check without overflow assumption — this is SAT (counterexample exists)
  __CPROVER_assert(a * c <= b * c, "mul monotone");
}
