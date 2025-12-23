#include <assert.h>
#include <math.h>

int main()
{
  double two = exp2(1.0);
  assert(two > 1.999 && two < 2.001);
  return 0;
}
