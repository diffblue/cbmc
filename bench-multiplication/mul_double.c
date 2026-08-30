#ifndef BW
#define BW 16
#endif
int main() {
  __CPROVER_bitvector[BW] a, b;
  __CPROVER_bitvector[BW/2] a_lo = a, b_lo = b, prod_lo = a * b;
  __CPROVER_assert(prod_lo == (__CPROVER_bitvector[BW/2])(a_lo * b_lo), "low half");
}
