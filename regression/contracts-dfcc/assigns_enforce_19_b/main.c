#include <assert.h>

static int b = 0;
static int c = 0;

int f(int *points_to_b, int *points_to_c) __CPROVER_assigns(b)
{
  // must pass
  b = 1;
  *points_to_b = 1;
  // must fail
  c = 2;
  *points_to_c = 2;
}

int main()
{
  f(&b, &c);
  return 0;
}
