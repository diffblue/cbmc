#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_isgreaterequalf();
  assert(0);
  return 0;
}
