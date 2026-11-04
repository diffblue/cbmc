#include <assert.h>
#include <math.h>

// Test float to fixedbv conversions
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Basic positive conversion
  float f1 = 10.5f;
  fixedbv_t fixed1 = (fixedbv_t)f1;
  assert(fixed1 > (fixedbv_t)10.49 && fixed1 < (fixedbv_t)10.51);

  // Basic negative conversion
  float f2 = -10.5f;
  fixedbv_t fixed2 = (fixedbv_t)f2;
  assert(fixed2 > (fixedbv_t)(-10.51) && fixed2 < (fixedbv_t)(-10.49));

  // Zero conversion
  float f3 = 0.0f;
  fixedbv_t fixed3 = (fixedbv_t)f3;
  assert(fixed3 == (fixedbv_t)0.0);

  // Integer value (no fraction)
  float f4 = 42.0f;
  fixedbv_t fixed4 = (fixedbv_t)f4;
  assert(fixed4 > (fixedbv_t)41.99 && fixed4 < (fixedbv_t)42.01);

  // Small fraction
  float f5 = 0.25f;
  fixedbv_t fixed5 = (fixedbv_t)f5;
  assert(fixed5 > (fixedbv_t)0.24 && fixed5 < (fixedbv_t)0.26);

  // Large value
  float f6 = 1000.75f;
  fixedbv_t fixed6 = (fixedbv_t)f6;
  assert(fixed6 > (fixedbv_t)1000.7 && fixed6 < (fixedbv_t)1000.8);

  // Negative small fraction
  float f7 = -0.25f;
  fixedbv_t fixed7 = (fixedbv_t)f7;
  assert(fixed7 > (fixedbv_t)(-0.26) && fixed7 < (fixedbv_t)(-0.24));

  // NaN handling - result should be zero or clamped
  float nan_val = NAN;
  fixedbv_t fixed_nan = (fixedbv_t)nan_val;
  // NaN conversion is implementation-defined, just check it doesn't crash

  // Infinity handling - result should be clamped to max
  float inf_val = INFINITY;
  fixedbv_t fixed_inf = (fixedbv_t)inf_val;
  // Infinity conversion should be clamped to max value

  return 0;
}
