#include <assert.h>

int main()
{
  int *p, o, n, x, x_before;
  x_before = x;
  p = &x;

  int result = __sync_val_compare_and_swap(p, o, n);
  assert(result == x_before);
  assert(x_before != o || x == n);
  assert(x_before == o || x == x_before);

  return 0;
}
