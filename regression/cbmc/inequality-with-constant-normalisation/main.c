// Tests that the normalisation of var ?= const works

#include <assert.h>

int main (void) {
  int x;

  while ((x >= 10) && (x < 10)) {}
  while ((x >= 10) && (x <= 9)) {}
  while ((x >= 10) && !(x > 9)) {}

  assert(x == x);

  return 0;
}
