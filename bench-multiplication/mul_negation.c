#ifndef BW
#define BW 16
#endif
int main() {
  __CPROVER_bitvector[BW] a;
  __CPROVER_assert(a * (__CPROVER_bitvector[BW])(-1) == -a, "mul by -1");
}
