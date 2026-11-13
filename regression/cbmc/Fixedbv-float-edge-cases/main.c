#include <assert.h>
#include <math.h>

// Test edge cases for fixedbv/float conversions
typedef __CPROVER_fixedbv[16][8] fixedbv_small_t;
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Test with very small positive value
  fixedbv_t fixed_tiny = (fixedbv_t)0.001;
  float f_tiny = (float)fixed_tiny;
  assert(f_tiny > 0.0f && f_tiny < 0.01f);

  // Test with very small negative value
  fixedbv_t fixed_tiny_neg = (fixedbv_t)(-0.001);
  float f_tiny_neg = (float)fixed_tiny_neg;
  assert(f_tiny_neg < 0.0f && f_tiny_neg > -0.01f);

  // Test conversion of positive zero
  fixedbv_t fixed_pos_zero = (fixedbv_t)0.0;
  float f_pos_zero = (float)fixed_pos_zero;
  assert(f_pos_zero == 0.0f);

  // Test round-trip with precision loss
  float original = 1.234567f;
  fixedbv_t fixed = (fixedbv_t)original;
  float roundtrip = (float)fixed;
  // Should be approximately equal (within fixedbv precision)
  assert(roundtrip > 1.23f && roundtrip < 1.25f);

  // Test boundary values for smaller fixedbv type
  fixedbv_small_t small_pos = (fixedbv_small_t)127.0;
  float f_small_pos = (float)small_pos;
  assert(f_small_pos > 126.9f && f_small_pos < 127.1f);

  fixedbv_small_t small_neg = (fixedbv_small_t)(-128.0);
  float f_small_neg = (float)small_neg;
  assert(f_small_neg > -128.1f && f_small_neg < -127.9f);

  // Test float to fixedbv with values that should fit
  float f_in_range = 50.5f;
  fixedbv_t fixed_in_range = (fixedbv_t)f_in_range;
  assert(fixed_in_range > (fixedbv_t)50.4 && fixed_in_range < (fixedbv_t)50.6);

  // Test float to fixedbv with truncation
  float f_trunc = 3.9999f;
  fixedbv_t fixed_trunc = (fixedbv_t)f_trunc;
  assert(fixed_trunc > (fixedbv_t)3.99 && fixed_trunc < (fixedbv_t)4.01);

  return 0;
}
