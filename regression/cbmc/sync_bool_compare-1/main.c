#include <assert.h>

int main()
{
  int *p, o, n, x, x_before;
  x_before = x;
  p = &x;

  _Bool result = __sync_bool_compare_and_swap(p, o, n);

  if(result)
    assert(o == x_before && x == n);
  else
    assert(o != x_before && x == x_before);

  return 0;
}
