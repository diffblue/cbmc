#include <assert.h>

int main()
{
  int i = 0, j = 0, k = 0;

  while(j < 10)
  {
    while(k < 10)
      __CPROVER_loop_invariant(1 == 1)
      {
        while(i < 10)
        {
          i++;
        }
      }
    j++;
  }
}
