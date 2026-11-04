#ifndef BW
#define BW 16
#endif
int main() {
  __CPROVER_bitvector[BW] a, b;
  __CPROVER_bitvector[BW*2] wide = (__CPROVER_bitvector[BW*2])a * (__CPROVER_bitvector[BW*2])b;
  __CPROVER_bitvector[BW] narrow = a * b;
  __CPROVER_assert(narrow == (__CPROVER_bitvector[BW])wide, "truncated matches wide");
}
