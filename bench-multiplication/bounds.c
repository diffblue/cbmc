#ifndef BW
#define BW 8
#endif
int main() {
  __CPROVER_bitvector[BW] a, b;
  __CPROVER_assume(a <= 10);
  __CPROVER_assume(b <= 10);
  __CPROVER_assert(a * b <= 100, "product bounded");
}
