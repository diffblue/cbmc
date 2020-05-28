#include <assert.h>

void entry_point(const int x)
{
  // expected to succeed
  assert(x - x == 0);

  // expected to fail
  assert(x != 13);
}
