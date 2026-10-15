#include <assert.h>

// Test round-trip conversions between fixedbv and float
typedef __CPROVER_fixedbv[32][16] fixedbv_t;

int main(void)
{
  // Test 1: fixedbv -> float -> fixedbv
  fixedbv_t original1 = (fixedbv_t)25.5;
  float f1 = (float)original1;
  fixedbv_t result1 = (fixedbv_t)f1;
  // Should be approximately equal (within precision)
  assert(result1 > (fixedbv_t)25.49 && result1 < (fixedbv_t)25.51);

  // Test 2: float -> fixedbv -> float
  float original2 = 37.25f;
  fixedbv_t fixed2 = (fixedbv_t)original2;
  float result2 = (float)fixed2;
  // Should be approximately equal
  assert(result2 > 37.24f && result2 < 37.26f);

  // Test 3: Negative round-trip
  fixedbv_t original3 = (fixedbv_t)(-18.75);
  float f3 = (float)original3;
  fixedbv_t result3 = (fixedbv_t)f3;
  assert(result3 > (fixedbv_t)(-18.76) && result3 < (fixedbv_t)(-18.74));

  // Test 4: Zero round-trip
  fixedbv_t original4 = (fixedbv_t)0.0;
  float f4 = (float)original4;
  fixedbv_t result4 = (fixedbv_t)f4;
  assert(result4 == (fixedbv_t)0.0);

  // Test 5: Small fractional value
  fixedbv_t original5 = (fixedbv_t)0.0625;
  float f5 = (float)original5;
  fixedbv_t result5 = (fixedbv_t)f5;
  assert(result5 > (fixedbv_t)0.0624 && result5 < (fixedbv_t)0.0626);

  // Test 6: Integer value
  fixedbv_t original6 = (fixedbv_t)1000.0;
  float f6 = (float)original6;
  fixedbv_t result6 = (fixedbv_t)f6;
  assert(result6 > (fixedbv_t)999.9 && result6 < (fixedbv_t)1000.1);

  // Test 7: Multiple conversions
  fixedbv_t start = (fixedbv_t)15.5;
  float temp1 = (float)start;
  fixedbv_t temp2 = (fixedbv_t)temp1;
  float temp3 = (float)temp2;
  fixedbv_t end = (fixedbv_t)temp3;
  assert(end > (fixedbv_t)15.49 && end < (fixedbv_t)15.51);

  return 0;
}
