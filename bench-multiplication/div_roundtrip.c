#ifndef BW
#define BW 8
#endif
int main() {
  unsigned __CPROVER_bitvector[BW] a, b;
  __CPROVER_assume(b != 0);
  unsigned __CPROVER_bitvector[BW] q = a / b;
  unsigned __CPROVER_bitvector[BW] r = a % b;
  __CPROVER_assert(q * b + r == a, "div roundtrip");
}
