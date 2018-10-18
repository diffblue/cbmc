#include <assert.h>
#include <stdlib.h>

int main()
{
  int *x = calloc(sizeof(int), 1);
  assert(*x == 0);
  return 0;
}
