#include <assert.h>

int main()
{
  int x = 0;

  do
    // clang-format off
   __CPROVER_assigns(x)
   __CPROVER_loop_invariant(0 <= x && x <= 10)
   __CPROVER_decreases(20 - x)
    // clang-format on
    {
      x++;
    }
  while(x < 10);

  assert(x == 10);
}
