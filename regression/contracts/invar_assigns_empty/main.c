#include <assert.h>

int main()
{
  while(1 == 1)
    __CPROVER_assigns() __CPROVER_loop_invariant(1 == 1)
    {
    }
}
