#include <assert.h>

int main()
{
  int *p, v, x, x_before;
  x_before = x;
  p = &x;

  int result = __sync_add_and_fetch(p, v);
  assert(result == x);
  assert(x == x_before + v);

  return 0;
}
