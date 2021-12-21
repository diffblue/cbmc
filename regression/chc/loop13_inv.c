#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;

  while (nondet_int())
  {
    int y = nondet_int();
    if (y == 0)
      x = x + y;
  }
  assert (x == 0);
}
