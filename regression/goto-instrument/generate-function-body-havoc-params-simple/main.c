#include <assert.h>
#include <stdlib.h>

void func(int *p);

void main()
{
  int i;
  i = 0;

  func(&i);

  assert(i == 0);
}
