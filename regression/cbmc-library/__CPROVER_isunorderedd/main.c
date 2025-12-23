#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_isunorderedd();
  assert(0);
  return 0;
}
