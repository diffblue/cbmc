#ifndef BW
#define BW 8
#endif
#define MOD (((__CPROVER_bitvector[BW])1 << (BW/2)) + 1)
int main() {
  __CPROVER_bitvector[BW] a, b;
  __CPROVER_assume(a < MOD);
  __CPROVER_assume(b < MOD);
  __CPROVER_bitvector[BW] p1 = (a * b) % MOD;
  __CPROVER_bitvector[BW] p2 = (b * a) % MOD;
  __CPROVER_assert(p1 == p2, "modular commutativity");
}
