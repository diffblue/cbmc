#include <assert.h>
#include <stdlib.h>

void entry_point(const int *x)
{
  if(x != NULL)
  {
    assert(*x - *x == 0);
  }
  // expected to fail because we should get non-null pointers
  assert(x == NULL);
}
