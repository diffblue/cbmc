#include <assert.h>
#include <float.h>

int main()
{
  __builtin_flt_rounds();
  assert(0);
  return 0;
}
