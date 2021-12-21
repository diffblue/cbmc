#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = nondet_int();
  __CPROVER_assume(-10 <= y && y <= 10);

  while (1)
  {
    if (y < 0)
    {
      
      break;
    }
    else if (y > 0)
    {
      x = x + y;
      assert(x > 0);
      y = -y;
      continue;
      int unused = 100;
      x = x - unused;
    }
    y++;
  }
  assert (x > 0);
}
