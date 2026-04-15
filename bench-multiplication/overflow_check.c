#ifndef BW
#define BW 16
#endif
int main() {
  __CPROVER_bitvector[BW] a, b;
  __CPROVER_bitvector[BW*2] wide_a = a, wide_b = b;
  __CPROVER_bitvector[BW*2] wide_product = wide_a * wide_b;
  __CPROVER_bitvector[BW] narrow_product = a * b;
  // Check: does the narrow product match the low bits of the wide product?
  __CPROVER_assert(narrow_product == (__CPROVER_bitvector[BW])wide_product, "no info loss");
}
