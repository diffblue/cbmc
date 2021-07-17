#include <stdio.h>

int ackermann(int m, int n);

int main()
{
  int m = 3;
  int n = 5;
  int result = ackermann(m, n);

  printf("Result of the Ackermann function: %d\n", result);
  return 0;
}

int ackermann(int m, int n)
  // clang-format off
__CPROVER_requires(0 <= m && 0 <= n)
__CPROVER_ensures(__CPROVER_return_value >= 0)
// clang-format on
{
  while(m > 0)
    // clang-format off
    __CPROVER_loop_invariant(0 <= m && 0 <= n)
    __CPROVER_decreases(m, n)
    // clang-format on
    {
      if(n == 0)
      {
        m--;
        n = 1;
      }
      else
      {
        n = ackermann(m, n - 1);
        m--;
      }
    }

  return n + 1;
}
