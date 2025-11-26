#define _USE_MATH_DEFINES
#include <assert.h>
#include <math.h>

int main()
{
  // sinf(0) = 0 exactly
  float s = sinf(0.0f);
  assert(s == 0.0f);

  // sinf(π/2) is in [0, 1]
  s = sinf(3.14159265f / 2.0f);
  assert(s >= 0.0f && s <= 1.0f);

  // sinf(-π/2) is in [-1, 0]
  s = sinf(-3.14159265f / 2.0f);
  assert(s >= -1.0f && s <= 0.0f);

  // sinf(π) is in [0, 1] (pi constant is at the boundary)
  s = sinf(3.14159265f);
  assert(s >= 0.0f && s <= 1.0f);

  // Range narrowing for [0, π]
  s = sinf(3.14159265f / 4.0f);
  assert(s >= 0.0f && s <= 1.0f);

  // Range narrowing for [π, 2π]
  s = sinf(5.0f * 3.14159265f / 4.0f);
  assert(s >= -1.0f && s <= 0.0f);

  return 0;
}
