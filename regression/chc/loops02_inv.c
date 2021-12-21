#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = 5;
  while (x < 5)
  {
    x++;
  }
  while (x < 10)
  {
    x++;
    y++;
  }
  assert(y == 10);
}
