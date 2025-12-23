#include <assert.h>
#include <math.h>

int main()
{
  __builtin_nan();
  assert(0);
  return 0;
}
