#include <assert.h>

int main()
{
  int *p, v, x, x_before;
  x_before = x;
  p = &x;

  int result = __atomic_fetch_add(p, v, 0);
  assert(result == x_before);
  assert(x == x_before + v);

  return 0;
}
