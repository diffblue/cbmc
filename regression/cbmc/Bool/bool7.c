#include <assert.h>

int main()
{
  _Bool u = 1;

  // assert the type of side effects on _Bool
  assert(sizeof(++u) == sizeof(_Bool));
  assert(sizeof(u += 1) == sizeof(_Bool));
  assert(sizeof(u = 1) == sizeof(_Bool));
}
