#ifndef BW
#define BW 9
#endif
int main() {
  __CPROVER_bitvector[BW] a, b, c;
  __CPROVER_bitvector[BW] lhs = a * (b + c), rhs = a * b + a * c;
  __CPROVER_assert(lhs == rhs, "distributivity");
}
