#define _USE_MATH_DEFINES
#include <assert.h>
#include <math.h>

int main()
{
  // cosf(0) = 1 exactly
  float c = cosf(0.0f);
  assert(c == 1.0f);

  // cosf(π) is in [-1, 0]
  c = cosf(3.14159265f);
  assert(c >= -1.0f && c <= 0.0f);

  // cosf(π/4) is in [0, 1]
  c = cosf(3.14159265f / 4.0f);
  assert(c >= 0.0f && c <= 1.0f);

  return 0;
}
