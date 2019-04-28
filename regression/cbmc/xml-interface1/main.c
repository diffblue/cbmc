#include <assert.h>

void foo(int x)
{
  for(int i = 0; i < 5; ++i)
  {
    if(x)
      assert(0);
    assert(0);
  }
  assert(0);
}
