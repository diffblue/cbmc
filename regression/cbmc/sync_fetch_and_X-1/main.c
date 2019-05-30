#include <assert.h>

int main()
{
  int *p, v, x, x_before;
  x_before = x;
  p = &x;

  int result = __sync_fetch_and_add(p, v);
  assert(result == x_before);
  assert(x == x_before + v);

  return 0;
}
