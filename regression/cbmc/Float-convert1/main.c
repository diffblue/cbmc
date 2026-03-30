// Based on Z3#4862: Float-to-double and double-to-float conversion.
// Verify that conversions preserve values correctly.

#include <assert.h>
#include <math.h>

int main()
{
  // float to double: exact for all finite floats
  float f = 3.14f;
  double d = (double)f;
  assert(d == (double)3.14f);

  // double to float: may lose precision
  double pi = 3.14159265358979323846;
  float pf = (float)pi;
  assert(pf == 3.14159265358979323846f);

  // NaN conversion
  float nan_f = NAN;
  double nan_d = (double)nan_f;
  assert(isnan(nan_d));

  // Infinity conversion
  float inf_f = INFINITY;
  double inf_d = (double)inf_f;
  assert(isinf(inf_d));

  return 0;
}
