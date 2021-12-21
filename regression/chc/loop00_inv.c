#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  do
  {
    x++;
  }
  while (x < 0);
  assert(x == 1);
}
