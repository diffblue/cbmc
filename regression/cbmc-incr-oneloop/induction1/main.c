#include <limits.h>

int main()
{
  signed x, y;
  while(1)
  {
    __CPROVER_assume(x >= 10);
    signed t = x;
    if((long)x + y <= INT_MAX)
      x = x + y;
    y = t;
    assert(x >= 10);
  }
}
