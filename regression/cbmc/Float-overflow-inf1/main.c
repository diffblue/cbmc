// Based on Z3#4673: Floating-point overflow should produce infinity.
// FLT_MAX * 2 overflows to +inf, then +inf * 0.5 = +inf.
// So (FLT_MAX * 2) * 0.5 > FLT_MAX should be satisfiable
// because +inf > FLT_MAX.

#include <assert.h>
#include <float.h>
#include <math.h>

int main()
{
  // FLT_MAX * 2 should overflow to +inf
  float x = FLT_MAX;
  float y = x * 2.0f;
  assert(isinf(y));
  assert(y > 0.0f);

  // +inf * 0.5 = +inf
  float z = y * 0.5f;
  assert(isinf(z));

  // +inf > FLT_MAX
  assert(z > x);

  return 0;
}
