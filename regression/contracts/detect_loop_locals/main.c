#include <stdlib.h>

int main()
{
  unsigned char *i = malloc(5);

  while(i != i + 5)
    __CPROVER_loop_invariant(1 == 1)
    {
      const char lower = *i++;
    }
}
