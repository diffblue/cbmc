#include <assert.h>

int main()
{
  int x = 0;

  do
  {
    x++;
  } while(x < 10) __CPROVER_loop_invariant(0 <= x && x <= 10);

  assert(x == 10);
}
