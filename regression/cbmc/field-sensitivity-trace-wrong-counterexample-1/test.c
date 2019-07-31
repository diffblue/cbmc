#include <assert.h>

struct SomeStruct
{
  int x;
};

int main(void)
{
  struct SomeStruct x;
  // this should cause
  // visible initialization of
  // x to value other than 0
  // if assertion fails
  assert(x.x == 0);
}
