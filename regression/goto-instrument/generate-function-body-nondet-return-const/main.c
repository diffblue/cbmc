#include <assert.h>

const int func();

void main()
{
  assert(func() == 0);
  assert(func() != 0);
}
