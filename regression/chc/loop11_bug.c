#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 10;
  int y = nondet_int();

  if (y > 0)
  {
    while (x >= 0)
    {
      if (x > y)
      {
        x = x - y;
      }
      else
      {
        x--;
      }
    }
    assert (x == 0);
  }
}
