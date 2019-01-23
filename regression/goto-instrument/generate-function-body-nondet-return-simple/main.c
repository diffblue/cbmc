#include <assert.h>

int func();

void main()
{
  assert(func() == 0);
  assert(func() != 0);
}
