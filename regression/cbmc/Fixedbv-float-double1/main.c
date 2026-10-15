#include <assert.h>

// Test fixedbv conversions with both float and double
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  fixedbv_t fixed_val = (fixedbv_t)123.456;

  // Convert to float
  float f = (float)fixed_val;
  assert(f > 123.45f && f < 123.47f);

  // Convert to double
  double d = (double)fixed_val;
  assert(d > 123.455 && d < 123.457);

  // Round-trip: fixedbv -> float -> fixedbv
  float f2 = (float)fixed_val;
  fixedbv_t fixed_roundtrip1 = (fixedbv_t)f2;
  assert(
    fixed_roundtrip1 > (fixedbv_t)123.45 &&
    fixed_roundtrip1 < (fixedbv_t)123.47);

  // Round-trip: fixedbv -> double -> fixedbv
  double d2 = (double)fixed_val;
  fixedbv_t fixed_roundtrip2 = (fixedbv_t)d2;
  assert(
    fixed_roundtrip2 > (fixedbv_t)123.45 &&
    fixed_roundtrip2 < (fixedbv_t)123.47);

  // Test with negative value
  fixedbv_t fixed_neg = (fixedbv_t)(-50.25);
  float f_neg = (float)fixed_neg;
  double d_neg = (double)fixed_neg;
  assert(f_neg > -50.26f && f_neg < -50.24f);
  assert(d_neg > -50.26 && d_neg < -50.24);

  return 0;
}
