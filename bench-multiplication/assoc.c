#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a, b, c;
  __CPROVER_bitvector[BW] ab = a * b, bc = b * c;
  __CPROVER_assert(ab * c == a * bc, "associativity");
}
