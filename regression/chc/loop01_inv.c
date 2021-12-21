#include <stdlib.h>
int nondet_int();

int main()
{
  for (int i = 0; i < 10; i++)
    i--;
  assert(0);
}
