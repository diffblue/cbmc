#include <assert.h>
#include <stdlib.h>

int main()
{
  int *x = malloc(2);
  int *y = malloc(2);
  assert(!__CPROVER_r_ok(x, 3));
  assert(__CPROVER_r_ok(x, 3) == __CPROVER_r_ok(y, 3));
}
