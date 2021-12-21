#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  while (x < 3)
  {
    int y = 0;
    while (y < 3)
    {
      y++;
    }
    x = x + y;
  }
  assert(x > 0);
}
