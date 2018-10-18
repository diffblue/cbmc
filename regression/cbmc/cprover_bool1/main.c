#include <assert.h>

int main()
{
  int y;
  __CPROVER_bool x = y;
  assert(x != (__CPROVER_bool)y);
}
