#ifndef BW
#define BW 16
#endif
int main() {
  __CPROVER_bitvector[BW] a;
  __CPROVER_assert(a * 4 == a << 2, "mul4 == shl2");
  __CPROVER_assert(a * 8 == a << 3, "mul8 == shl3");
}
