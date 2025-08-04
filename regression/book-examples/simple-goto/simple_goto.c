#include <assert.h>
#include <stdbool.h>

void foo(bool arg1, bool arg2)
{
  bool v1 = false;
  bool v2 = false;
  if(arg1)
    goto l1;
  v1 = true;
l1:
  if(arg2)
    goto l2;
  v2 = true;
l2:
  assert(v1);
  assert(v2);
}
