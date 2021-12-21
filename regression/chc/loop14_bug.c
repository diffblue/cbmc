#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;

  while (nondet_int())
  {
    int y = nondet_int();
    if (x >= 0 && x < 10)
    {
      if (y >= 0 && y < 10)
      {
        x = x + y;
      }
      else if (y >= -10 && y <= 0)
      {
        x = x - y;
      }
    }
  }
  assert (x > 0);
}
