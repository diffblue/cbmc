#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = 5;
  for (int i = 0; i < 10; i++)
  {
    if (x >= 5) y++;
    x++;
  }
  assert(y == 10);
}
