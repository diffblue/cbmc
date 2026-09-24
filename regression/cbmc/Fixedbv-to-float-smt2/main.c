#include <assert.h>

// Test fixedbv to float conversions with SMT2 backend
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Test basic conversion
  fixedbv_t fixed1 = (fixedbv_t)5.5;
  float f1 = (float)fixed1;
  assert(f1 > 5.49f && f1 < 5.51f);

  // Test negative conversion
  fixedbv_t fixed2 = (fixedbv_t)(-7.25);
  float f2 = (float)fixed2;
  assert(f2 > -7.26f && f2 < -7.24f);

  // Test zero
  fixedbv_t fixed3 = (fixedbv_t)0.0;
  float f3 = (float)fixed3;
  assert(f3 == 0.0f);

  // Test fractional value
  fixedbv_t fixed4 = (fixedbv_t)0.125;
  float f4 = (float)fixed4;
  assert(f4 > 0.124f && f4 < 0.126f);

  // Test integer value
  fixedbv_t fixed5 = (fixedbv_t)100.0;
  float f5 = (float)fixed5;
  assert(f5 > 99.9f && f5 < 100.1f);

  return 0;
}
