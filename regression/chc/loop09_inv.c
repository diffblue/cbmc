#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = nondet_int();

  if (y >= 0)
  {
    do
    {
      if (x == y)
      {
        y++;
      }
      else
      {
        x = x + y;
      }
    }
    while (x == 0);
    assert (y > 0);
  }
}
