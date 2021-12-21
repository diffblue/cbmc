#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0;
  for(int i = 0; i < 3; i++)
    for(int j = 0; j < 3; j++)
      for(int k = 0; k < 3; k++)
        x++;

  assert(x == 27);
}
