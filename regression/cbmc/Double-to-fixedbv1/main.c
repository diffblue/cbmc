#include <assert.h>
#include <math.h>

// Test double to fixedbv conversions
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Basic positive conversion
  double d1 = 10.5;
  fixedbv_t fixed1 = (fixedbv_t)d1;
  assert(fixed1 > (fixedbv_t)10.49 && fixed1 < (fixedbv_t)10.51);

  // Basic negative conversion
  double d2 = -10.5;
  fixedbv_t fixed2 = (fixedbv_t)d2;
  assert(fixed2 > (fixedbv_t)(-10.51) && fixed2 < (fixedbv_t)(-10.49));

  // Zero conversion
  double d3 = 0.0;
  fixedbv_t fixed3 = (fixedbv_t)d3;
  assert(fixed3 == (fixedbv_t)0.0);

  // High precision value
  double d4 = 123.456;
  fixedbv_t fixed4 = (fixedbv_t)d4;
  assert(fixed4 > (fixedbv_t)123.455 && fixed4 < (fixedbv_t)123.457);

  // Small fraction
  double d5 = 0.0625;
  fixedbv_t fixed5 = (fixedbv_t)d5;
  assert(fixed5 > (fixedbv_t)0.0624 && fixed5 < (fixedbv_t)0.0626);

  // Large value
  double d6 = 5000.125;
  fixedbv_t fixed6 = (fixedbv_t)d6;
  assert(fixed6 > (fixedbv_t)5000.12 && fixed6 < (fixedbv_t)5000.13);

  // Negative fractional
  double d7 = -0.75;
  fixedbv_t fixed7 = (fixedbv_t)d7;
  assert(fixed7 > (fixedbv_t)(-0.76) && fixed7 < (fixedbv_t)(-0.74));

  // NaN handling
  double nan_val = NAN;
  fixedbv_t fixed_nan = (fixedbv_t)nan_val;
  // NaN conversion is implementation-defined

  // Infinity handling
  double inf_val = INFINITY;
  fixedbv_t fixed_inf = (fixedbv_t)inf_val;
  // Infinity should be clamped to max value

  return 0;
}
