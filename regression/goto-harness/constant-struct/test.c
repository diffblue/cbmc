#include <stdlib.h>

struct SomeStruct
{
  int x;
};

void entry_point(const struct SomeStruct value)
{
  assert(value.x - value.x == 0);
  assert(value.x != 13);
}
