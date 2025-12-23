#include <assert.h>
#include <math.h>

int main()
{
  assert(trunc(1.1) == 1.0);
  assert(trunc(1.9) == 1.0);
  assert(trunc(-1.1) == -1.0);
  assert(trunc(-1.9) == -1.0);
  assert(signbit(trunc(-0.0)));
  return 0;
}
