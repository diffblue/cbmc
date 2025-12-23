#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_islessgreaterf();
  assert(0);
  return 0;
}
