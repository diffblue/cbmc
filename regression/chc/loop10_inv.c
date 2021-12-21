#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = nondet_int();

  while (1)
  {
    if (y < 0)
    {
      y = -y;
    }
    else
    {
      x = x + y;
      assert(x >= 0);
      break;
      int unused = 50;
      x = x - unused;
    }
  }
  assert (x >= 0);
}
