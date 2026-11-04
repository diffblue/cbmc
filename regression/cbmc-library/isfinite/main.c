#include <assert.h>
#include <math.h>

int main()
{
  assert(isfinite(1.0));
  assert(isfinite(1.0f));
  assert(isfinite(1.0l));
  float f;
  assert(
    !!isfinite(f) == (fpclassify(f) != FP_NAN && fpclassify(f) != FP_INFINITE));
  double d;
  assert(
    !!isfinite(d) == (fpclassify(d) != FP_NAN && fpclassify(d) != FP_INFINITE));
  long double ld;
  assert(
    !!isfinite(ld) ==
    (fpclassify(ld) != FP_NAN && fpclassify(ld) != FP_INFINITE));
  return 0;
}
