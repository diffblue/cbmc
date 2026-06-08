#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a, b, c;
  __CPROVER_assert(a * (b + c) == a * b + a * c, "distributivity");
}
