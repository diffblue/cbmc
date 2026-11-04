#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{
  size_t x = __VERIFIER_nondet_size_t();
  size_t y = __VERIFIER_nondet_size_t();
  uint8_t *a;

  __CPROVER_assume(x > 0);
  __CPROVER_assume(y > x);

  a = malloc(sizeof(uint8_t) * x);

  assert(__CPROVER_w_ok(a, x));
  assert(!__CPROVER_w_ok(a, y));
}
