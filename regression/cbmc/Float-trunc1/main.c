// Based on Z3#4841: truncation (roundToIntegral RTZ) correctness.
// truncf(3.5f) should be 3.0f, truncf(-2.7f) should be -2.0f.

#include <assert.h>
#include <math.h>

int main()
{
  assert(truncf(3.5f) == 3.0f);
  assert(truncf(-2.7f) == -2.0f);
  assert(truncf(0.0f) == 0.0f);
  assert(truncf(-0.0f) == -0.0f);

  // truncf of integer is identity
  assert(truncf(5.0f) == 5.0f);

  // truncf of NaN is NaN
  assert(isnan(truncf(NAN)));

  // truncf of Inf is Inf
  assert(isinf(truncf(INFINITY)));

  return 0;
}
