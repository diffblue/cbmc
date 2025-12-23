#include <assert.h>
#include <math.h>

int main()
{
  assert(floor(1.1) == 1.0);
  assert(floor(1.9) == 1.0);
  assert(floor(-1.1) == -2.0);
  assert(floor(-1.9) == -2.0);
  assert(signbit(floor(-0.0)));
  return 0;
}
