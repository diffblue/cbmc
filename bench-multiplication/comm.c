#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a, b;
  __CPROVER_bitvector[BW] c = a * b, d = b * a;
  __CPROVER_assert(c == d, "commutativity");
}
