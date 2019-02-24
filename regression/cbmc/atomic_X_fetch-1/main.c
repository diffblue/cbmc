#include <assert.h>

int main()
{
  int *p, v, x, x_before;
  x_before = x;
  p = &x;

  int result = __atomic_add_fetch(p, v, 0);
  assert(result == x);
  assert(x == x_before + v);

  return 0;
}
