#include <assert.h>
#include <math.h>

int main()
{
  assert(roundf(1.1f) == 1.0f);
  assert(roundf(1.5f) == 2.0f);
  assert(roundf(1.9f) == 2.0f);
  assert(roundf(-1.1f) == -1.0f);
  assert(roundf(-1.5f) == -2.0f);
  assert(roundf(-1.9f) == -2.0f);
  assert(signbit(roundf(-0.0f)));
  return 0;
}
