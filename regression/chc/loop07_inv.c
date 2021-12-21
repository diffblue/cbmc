#include <stdlib.h>
int nondet_int();

int main()
{
  int x = nondet_int();
  int y = nondet_int();
  __CPROVER_assume (x >= 0 && y >= 0 && x < 10 && y < 10);

  for (int i = 0; i < 10; i++)
  {
    if (x > y)
    {
      y++;
    }
    else if (x < y)
    {
      x++;
    }
    else
    {
      x++;
      y++;
    }
  }
  assert(y == x);
}
