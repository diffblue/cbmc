#include <assert.h>

// Test float to fixedbv conversions with SMT2 backend
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Test basic conversion
  float f1 = 5.5f;
  fixedbv_t fixed1 = (fixedbv_t)f1;
  assert(fixed1 > (fixedbv_t)5.49 && fixed1 < (fixedbv_t)5.51);

  // Test negative conversion
  float f2 = -7.25f;
  fixedbv_t fixed2 = (fixedbv_t)f2;
  assert(fixed2 > (fixedbv_t)(-7.26) && fixed2 < (fixedbv_t)(-7.24));

  // Test zero
  float f3 = 0.0f;
  fixedbv_t fixed3 = (fixedbv_t)f3;
  assert(fixed3 == (fixedbv_t)0.0);

  // Test fractional value
  float f4 = 0.125f;
  fixedbv_t fixed4 = (fixedbv_t)f4;
  assert(fixed4 > (fixedbv_t)0.124 && fixed4 < (fixedbv_t)0.126);

  // Test integer value
  float f5 = 100.0f;
  fixedbv_t fixed5 = (fixedbv_t)f5;
  assert(fixed5 > (fixedbv_t)99.9 && fixed5 < (fixedbv_t)100.1);

  return 0;
}
