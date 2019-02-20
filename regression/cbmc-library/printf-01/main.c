#include <assert.h>
#include <stdio.h>

int main()
{
  int x;
  x = printf("x");
  assert(x < 0);
  return 0;
}
