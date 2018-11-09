#include <assert.h>
#include <math.h>

int main()
{
  __builtin_inf();
  assert(0);
  return 0;
}
