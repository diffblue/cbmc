#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  for (int i = 0; i < 3; i++)
  {
    if (i == 1) continue;
    for (int j = 0; j < 3; j++)
    {
      if (j == 2) continue;
      x++;
    }
  }
  assert(x == 4);
}
