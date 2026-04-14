#ifndef BW
#define BW 16
#endif
int main() {
  __CPROVER_bitvector[BW/2] a, b;
  __CPROVER_bitvector[BW] wide = (__CPROVER_bitvector[BW])a * (__CPROVER_bitvector[BW])b;
  __CPROVER_bitvector[BW*2] wider = (__CPROVER_bitvector[BW*2])a * (__CPROVER_bitvector[BW*2])b;
  __CPROVER_assert(wide == (__CPROVER_bitvector[BW])wider, "no overflow");
}
