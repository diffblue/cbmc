#include <assert.h>

struct SomeStruct
{
  const int x;
};

void entry_point(struct SomeStruct value)
{
  // expected to succeed
  assert(value.x - value.x == 0);

  // expected to fail
  assert(value.x != 13);
}
