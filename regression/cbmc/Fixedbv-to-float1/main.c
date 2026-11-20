#include <assert.h>

// Test fixedbv to float conversions
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Basic positive conversion
  fixedbv_t fixed_pos = (fixedbv_t)10.5;
  float f1 = (float)fixed_pos;
  assert(f1 > 10.49f && f1 < 10.51f);

  // Basic negative conversion
  fixedbv_t fixed_neg = (fixedbv_t)(-10.5);
  float f2 = (float)fixed_neg;
  assert(f2 > -10.51f && f2 < -10.49f);

  // Zero conversion
  fixedbv_t fixed_zero = (fixedbv_t)0.0;
  float f3 = (float)fixed_zero;
  assert(f3 == 0.0f);

  // Integer value (no fraction)
  fixedbv_t fixed_int = (fixedbv_t)42.0;
  float f4 = (float)fixed_int;
  assert(f4 > 41.99f && f4 < 42.01f);

  // Small fraction
  fixedbv_t fixed_small = (fixedbv_t)0.25;
  float f5 = (float)fixed_small;
  assert(f5 > 0.24f && f5 < 0.26f);

  // Large value
  fixedbv_t fixed_large = (fixedbv_t)1000.75;
  float f6 = (float)fixed_large;
  assert(f6 > 1000.7f && f6 < 1000.8f);

  // Negative small fraction
  fixedbv_t fixed_neg_small = (fixedbv_t)(-0.25);
  float f7 = (float)fixed_neg_small;
  assert(f7 > -0.26f && f7 < -0.24f);

  return 0;
}
