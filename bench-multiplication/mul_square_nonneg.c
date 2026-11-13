#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a;
  __CPROVER_bitvector[BW*2] wide = (__CPROVER_bitvector[BW*2])a * (__CPROVER_bitvector[BW*2])a;
  __CPROVER_assert(wide >= a, "square >= original");
}
