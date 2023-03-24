#include <assert.h>

int main()
{
  int x = 0;

  while(x < 10)
    __CPROVER_loop_invariant(0 <= x && x <= 10);
  {
    x++;
  }

  assert(x == 10);
}
