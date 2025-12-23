#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_isgreaterf();
  assert(0);
  return 0;
}
