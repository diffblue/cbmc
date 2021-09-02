#include <assert.h>

int main()
{
  int x;
  __CPROVER_assume(x > 0);
  __CPROVER_assume(x < 0);
  assert(0 == 1);
}
