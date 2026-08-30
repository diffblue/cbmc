#ifndef BW
#define BW 8
#endif
int main() {
  __CPROVER_bitvector[BW] a, b, r;
  r = a * b;
  __CPROVER_assume(r == 0);
  __CPROVER_assume(a != 0);
  __CPROVER_assume(b != 0);
  __CPROVER_assert(0, "found zero divisors");
}
