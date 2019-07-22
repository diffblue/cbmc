#include <assert.h>

void foo(void *arg)
{
  assert(*(unsigned *)(arg) == 5);
}
