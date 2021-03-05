#include <assert.h>

int main()
{
  int r, n, x, y;
  __CPROVER_assume(n > 0 && x == y);

  for(r = 0; r < n; ++r)
    __CPROVER_loop_invariant(0 <= r && r <= n && x == y + r)
    {
      x++;
    }
  while(r > 0)
    __CPROVER_loop_invariant(r >= 0 && x == y + n + (n - r))
    {
      y--;
      r--;
    }

  assert(x == y + 2 * n);

  return 0;
}
