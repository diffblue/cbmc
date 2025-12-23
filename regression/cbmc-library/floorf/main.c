#include <assert.h>
#include <math.h>

int main()
{
  assert(floorf(1.1f) == 1.0f);
  assert(floorf(1.9f) == 1.0f);
  assert(floorf(-1.1f) == -2.0f);
  assert(floorf(-1.9f) == -2.0f);
  assert(signbit(floorf(-0.0f)));
  return 0;
}
