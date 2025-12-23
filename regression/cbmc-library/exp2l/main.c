#include <assert.h>
#include <math.h>

int main()
{
  long double two = exp2l(1.0l);
  assert(two > 1.999l && two < 2.001l);
  return 0;
}
