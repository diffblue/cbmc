#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a;
  __CPROVER_assert(a * 3 == a + a + a, "multiply by 3");
}
