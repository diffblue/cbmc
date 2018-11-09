#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_islessequald();
  assert(0);
  return 0;
}
