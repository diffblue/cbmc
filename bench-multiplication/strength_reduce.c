#ifndef BW
#define BW 16
#endif
int main() {
  __CPROVER_bitvector[BW] x;
  __CPROVER_assert(x * 15 == (x << 4) - x, "strength reduction");
}
