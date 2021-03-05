#include <assert.h>

int main()
{
  int n, s = 0;
  __CPROVER_assume(n >= 0);

  for(int i = 0; i < n; ++i)
    __CPROVER_loop_invariant(i <= n && s == i)
    {
      int a, b;
      __CPROVER_assume(b >= 0 && a == b);

      while(a > 0)
        __CPROVER_loop_invariant(a >= 0 && s == i + (b - a))
        {
          s++;
          a--;
        }

      s -= (b - 1);
    }

  assert(s == n);

  return 0;
}
