#include <assert.h>
#include <math.h>

// Test float to fixedbv overflow and clamping behavior
typedef __CPROVER_fixedbv
  [16][8] fixedbv_small_t; // Small type for easier overflow testing

int main(void)
{
  // Test value that fits within range
  float f1 = 50.5f;
  fixedbv_small_t fixed1 = (fixedbv_small_t)f1;
  assert(fixed1 > (fixedbv_small_t)50.4 && fixed1 < (fixedbv_small_t)50.6);

  // Test large positive value (potential overflow)
  // For 16-bit fixedbv with 8 fraction bits: max ~= 127.99
  float f2 = 127.0f;
  fixedbv_small_t fixed2 = (fixedbv_small_t)f2;
  assert(fixed2 > (fixedbv_small_t)126.9 && fixed2 < (fixedbv_small_t)127.1);

  // Test large negative value (potential underflow)
  // Min ~= -128.0
  float f3 = -128.0f;
  fixedbv_small_t fixed3 = (fixedbv_small_t)f3;
  assert(fixed3 == (fixedbv_small_t)(-128.0));

  // Test value very close to zero
  float f4 = 0.01f;
  fixedbv_small_t fixed4 = (fixedbv_small_t)f4;
  assert(fixed4 > (fixedbv_small_t)0.0 && fixed4 < (fixedbv_small_t)0.02);

  // Test negative value close to zero
  float f5 = -0.01f;
  fixedbv_small_t fixed5 = (fixedbv_small_t)f5;
  assert(fixed5 > (fixedbv_small_t)(-0.02) && fixed5 < (fixedbv_small_t)0.0);

  // Test positive infinity (should be clamped)
  float inf_pos = INFINITY;
  fixedbv_small_t fixed_inf_pos = (fixedbv_small_t)inf_pos;
  // Should be clamped to max value (implementation-defined behavior)

  // Test negative infinity (should be clamped)
  float inf_neg = -INFINITY;
  fixedbv_small_t fixed_inf_neg = (fixedbv_small_t)inf_neg;
  // Should be clamped to min value (implementation-defined behavior)

  // Test NaN (should result in zero or implementation-defined value)
  float nan_val = NAN;
  fixedbv_small_t fixed_nan = (fixedbv_small_t)nan_val;
  // NaN handling is implementation-defined

  return 0;
}
