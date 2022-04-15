#include <assert.h>
#include <stdbool.h>

int main()
{
  unsigned n, k, sum_to_k = 0;
  bool flag = false;

  for(unsigned i = 0; i < n; ++i)
    // clang-format off
  __CPROVER_loop_invariant(0 <= i && i <= n)
    // clang-format on
    {
      if(i == k)
      {
        flag = true;
        break;
      }
      sum_to_k += i;
    }
}
