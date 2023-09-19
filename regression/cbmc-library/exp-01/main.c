#include <assert.h>
#include <math.h>

int main()
{
  double e = exp(1.0);
  assert(e > 2.713 && e < 2.886);
  return 0;
}
