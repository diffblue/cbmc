#include <assert.h>
#include <math.h>

int main()
{
  assert(1.0 / 2 == 0.5);
  assert(1.0 / 0 == INFINITY);
  assert(-1.0 / 0 == -INFINITY);
  assert(isnan(NAN / 0));
  assert(1.0 / INFINITY == 0);
  assert(isnan(INFINITY / INFINITY));
}
