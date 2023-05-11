#include <assert.h>

int foo(int x)
{
  return x;
}

int main()
{
  int i, n, x[10];
  __CPROVER_assume(x[0] == x[9]);
  while(i < n)
    __CPROVER_loop_invariant(x[0] == __CPROVER_loop_entry(foo(x[0])))
    {
      x[0] = x[9] - 1;
      x[0]++;
    }
  assert(x[0] == x[9]);
}
