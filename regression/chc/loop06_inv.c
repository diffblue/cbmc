#include <stdlib.h>
int nondet_int();

int main()
{
  int x = nondet_int();
  int y = nondet_int();
  __CPROVER_assume (x < 100 && y < 100);

  for (int i = 0; i < 10; i++)
  {
    if (x == y)
    {
      x++;
      y++;
    }
    else
    {
      x = y;
    }
  }
  assert(y == x);
}
