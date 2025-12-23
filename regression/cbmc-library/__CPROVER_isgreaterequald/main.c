#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_isgreaterequald();
  assert(0);
  return 0;
}
