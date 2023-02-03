#include <stdbool.h>
#include <stdlib.h>

void main()
{
  long x = 0;
  long y;
  __CPROVER_assume(y > 1);

  while(y > 0)
  {
    x = 1;
    y = y - 1;
  }

  assert(false);
}
