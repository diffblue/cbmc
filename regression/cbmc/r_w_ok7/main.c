#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{
  size_t x;
  size_t y;
  uint8_t *a;

  __CPROVER_assume(x > 0);
  __CPROVER_assume(y > x);

  a = malloc(sizeof(uint8_t) * x);

  assert(__CPROVER_w_ok(a, x));
  assert(!__CPROVER_w_ok(a, y));
}
