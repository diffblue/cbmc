#include <stdlib.h>
#define ROW 10

void boo(int *x)
{
  *x = *x + 1;
}

void main()
{
  int *x = (int *)malloc(sizeof(int));
  int buffer[ROW];
  *x = 2;
  // not shrinkable since x has a self-update in boo()
  for(int i = 0; i < ROW; i++)
  {
    boo(x);
    buffer[*x] = 1;
  }
}
