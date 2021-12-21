#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = 5;
  int b = 0;
  for (int i = 0; i < 10; i++)
  {
    int z = x;
    if (z == 5) b = 1;
    if (b) y--;
    x++;
  }
  assert(y == 0);
}
