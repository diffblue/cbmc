// Tests that the normalisation of var ?= const works

#include <assert.h>

int main (void) {
  int x = __VERIFIER_nondet_int();

  while ((x >= 10) && (x < 10)) {}
  while ((x >= 10) && (x <= 9)) {}
  while ((x >= 10) && !(x > 9)) {}

  assert(x == x);

  return 0;
}
