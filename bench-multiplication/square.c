#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a, b;
  __CPROVER_bitvector[BW] sum = a + b;
  __CPROVER_assert(sum * sum == a*a + (__CPROVER_bitvector[BW])2*a*b + b*b, "square identity");
}
