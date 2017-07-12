#include <stdlib.h>
#include <assert.h>

int main()
{
  int *x=calloc(sizeof(int), 1);
  assert(*x==0);
  return 0;
}
