#include <assert.h>
#include <math.h>

int main()
{
  __CPROVER_isunorderedf();
  assert(0);
  return 0;
}
