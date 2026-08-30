#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a, b, s = a + b;
  __CPROVER_bitvector[BW] lhs = s * s;
  __CPROVER_bitvector[BW] rhs = a*a + (__CPROVER_bitvector[BW])2*a*b + b*b;
  __CPROVER_assert(lhs == rhs, "square identity");
}
