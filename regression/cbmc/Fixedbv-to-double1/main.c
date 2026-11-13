#include <assert.h>

// Test fixedbv to double conversions
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Basic positive conversion
  fixedbv_t fixed_pos = (fixedbv_t)10.5;
  double d1 = (double)fixed_pos;
  assert(d1 > 10.49 && d1 < 10.51);

  // Basic negative conversion
  fixedbv_t fixed_neg = (fixedbv_t)(-10.5);
  double d2 = (double)fixed_neg;
  assert(d2 > -10.51 && d2 < -10.49);

  // Zero conversion
  fixedbv_t fixed_zero = (fixedbv_t)0.0;
  double d3 = (double)fixed_zero;
  assert(d3 == 0.0);

  // High precision value
  fixedbv_t fixed_prec = (fixedbv_t)123.456;
  double d4 = (double)fixed_prec;
  assert(d4 > 123.455 && d4 < 123.457);

  // Small fraction
  fixedbv_t fixed_small = (fixedbv_t)0.0625;
  double d5 = (double)fixed_small;
  assert(d5 > 0.0624 && d5 < 0.0626);

  // Large value
  fixedbv_t fixed_large = (fixedbv_t)5000.125;
  double d6 = (double)fixed_large;
  assert(d6 > 5000.12 && d6 < 5000.13);

  // Negative fractional
  fixedbv_t fixed_neg_frac = (fixedbv_t)(-0.75);
  double d7 = (double)fixed_neg_frac;
  assert(d7 > -0.76 && d7 < -0.74);

  return 0;
}
