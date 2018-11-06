#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_isgreaterd();
  assert(0);
  return 0;
}
