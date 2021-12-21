#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  int y = nondet_int();

  for (int i = 0; i < 10; i++)
  {
    if (y > 10) continue;
    if (y <= 0) continue;
    x = x + y;
    assert(x >= i);
  }
}
