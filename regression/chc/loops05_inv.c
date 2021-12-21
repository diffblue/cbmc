#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  while (1)
  {
    x++;
    if (x == 5) break;
    while (1)
    {
      if (x >= 2) break;
      x = x + 2;
    }
  }
  assert(x == 5);
}
