#include <stdlib.h>
int nondet_int();

int main()
{
  int x = 0; 
  for (int i = 0; i < 10; i++)
    x++;
  assert(x == 10);
}
