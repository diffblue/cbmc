// SV-COMP style: unsigned multiplication overflow check
#ifndef BW
#define BW 16
#endif
int main() {
  unsigned __CPROVER_bitvector[BW] a, b;
  unsigned __CPROVER_bitvector[BW*2] wide = (unsigned __CPROVER_bitvector[BW*2])a * (unsigned __CPROVER_bitvector[BW*2])b;
  unsigned __CPROVER_bitvector[BW] narrow = a * b;
  // If no overflow, wide and narrow should match
  __CPROVER_assume(wide == (unsigned __CPROVER_bitvector[BW*2])narrow);
  // Under no-overflow assumption, commutativity holds trivially
  // But let's check a more interesting property:
  // If a*b doesn't overflow, then a <= MAX/b (when b != 0)
  unsigned __CPROVER_bitvector[BW] max_val = ~(unsigned __CPROVER_bitvector[BW])0;
  __CPROVER_assume(b != 0);
  __CPROVER_assert(a <= max_val / b, "overflow implies bound");
}
