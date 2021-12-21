#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = nondet_int();
  if (y > 0)
  {
    while (x < 5)
    {
      x = x + y;
    }
  }
  else
  {
    while (x > 5)
    {
      x = x - y;
    }
  }
  assert(x > 0);
}
