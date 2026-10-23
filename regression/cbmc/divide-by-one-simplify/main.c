#include <assert.h>

int main (void) {
  float f = __VERIFIER_nondet_float();
  float g;
  int i;

  __CPROVER_assume(f == f); // I.E. not NaN

  g = f;
  for (i = 0; i < 10000; ++i) {
    g /= 1.0f;
  }

  assert(f == g);

  return 1;
}
