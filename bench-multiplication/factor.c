#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] p, q;
  __CPROVER_assume(p > 1 && q > 1);
  __CPROVER_assert(p * q != 143, "not factorable");
}
