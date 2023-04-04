#include <assert.h>
#include <stdlib.h>

int main()
{
  int *x = calloc(sizeof(int), 2);
  assert(*x == 0);
  return 0;
}
