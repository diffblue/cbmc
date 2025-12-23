#include <assert.h>
#include <math.h>

int main()
{
  assert(truncf(1.1f) == 1.0f);
  assert(truncf(1.9f) == 1.0f);
  assert(truncf(-1.1f) == -1.0f);
  assert(truncf(-1.9f) == -1.0f);
  assert(signbit(trunc(-0.0f)));
  return 0;
}
