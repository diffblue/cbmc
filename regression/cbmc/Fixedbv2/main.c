#include <assert.h>

main() {
  __CPROVER_fixedbv[32][16] a;
  __CPROVER_fixedbv[64][32] b;

  a=1.25L;
  assert(a==(__CPROVER_fixedbv[32][16])1.25);

  b=1.250;
  assert(b==(__CPROVER_fixedbv[64][32])1.25);
}
