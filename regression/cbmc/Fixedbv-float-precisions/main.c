#include <assert.h>

// Test fixedbv/float conversions with different precisions
typedef __CPROVER_fixedbv[16]
                         [8] fixedbv_16_8_t; // 16 bits total, 8 fraction bits
typedef __CPROVER_fixedbv
  [32][16] fixedbv_32_16_t; // 32 bits total, 16 fraction bits
typedef __CPROVER_fixedbv
  [24][12] fixedbv_24_12_t; // 24 bits total, 12 fraction bits

int main(void)
{
  // Test with 16-bit fixedbv (8 fraction bits)
  fixedbv_16_8_t fixed_16 = (fixedbv_16_8_t)10.25;
  float f_16 = (float)fixed_16;
  assert(f_16 > 10.24f && f_16 < 10.26f);

  fixedbv_16_8_t roundtrip_16 = (fixedbv_16_8_t)f_16;
  assert(
    roundtrip_16 > (fixedbv_16_8_t)10.24 &&
    roundtrip_16 < (fixedbv_16_8_t)10.26);

  // Test with 32-bit fixedbv (16 fraction bits)
  fixedbv_32_16_t fixed_32 = (fixedbv_32_16_t)10.25;
  float f_32 = (float)fixed_32;
  assert(f_32 > 10.24f && f_32 < 10.26f);

  fixedbv_32_16_t roundtrip_32 = (fixedbv_32_16_t)f_32;
  assert(
    roundtrip_32 > (fixedbv_32_16_t)10.24 &&
    roundtrip_32 < (fixedbv_32_16_t)10.26);

  // Test with 24-bit fixedbv (12 fraction bits)
  fixedbv_24_12_t fixed_24 = (fixedbv_24_12_t)10.25;
  float f_24 = (float)fixed_24;
  assert(f_24 > 10.24f && f_24 < 10.26f);

  fixedbv_24_12_t roundtrip_24 = (fixedbv_24_12_t)f_24;
  assert(
    roundtrip_24 > (fixedbv_24_12_t)10.24 &&
    roundtrip_24 < (fixedbv_24_12_t)10.26);

  // Test negative values with different precisions
  fixedbv_16_8_t fixed_16_neg = (fixedbv_16_8_t)(-5.5);
  float f_16_neg = (float)fixed_16_neg;
  assert(f_16_neg > -5.51f && f_16_neg < -5.49f);

  fixedbv_32_16_t fixed_32_neg = (fixedbv_32_16_t)(-5.5);
  float f_32_neg = (float)fixed_32_neg;
  assert(f_32_neg > -5.51f && f_32_neg < -5.49f);

  fixedbv_24_12_t fixed_24_neg = (fixedbv_24_12_t)(-5.5);
  float f_24_neg = (float)fixed_24_neg;
  assert(f_24_neg > -5.51f && f_24_neg < -5.49f);

  // Test fractional precision differences
  float precise_val = 1.234567f;

  fixedbv_16_8_t fixed_16_prec = (fixedbv_16_8_t)precise_val;
  float f_16_prec = (float)fixed_16_prec;
  assert(f_16_prec > 1.23f && f_16_prec < 1.25f);

  fixedbv_32_16_t fixed_32_prec = (fixedbv_32_16_t)precise_val;
  float f_32_prec = (float)fixed_32_prec;
  assert(f_32_prec > 1.23f && f_32_prec < 1.25f);

  return 0;
}
