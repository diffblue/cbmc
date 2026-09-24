// Test case for bug fix: inf / inf SHOULD trigger --nan-check failure
// According to IEEE 754-2019, inf/inf produces NaN

#include <assert.h>
#include <math.h>

int main(void)
{
  // Ensure infinity / infinity produces NaN and triggers nan-check
  float inf1 = INFINITY;
  float inf2 = INFINITY;
  float result1 = inf1 / inf2; // Should trigger NaN check
  assert(isnan(result1));

  // Also test -inf / inf
  float result2 = (-INFINITY) / INFINITY; // Should trigger NaN check
  assert(isnan(result2));

  // And inf / -inf
  float result3 = INFINITY / (-INFINITY); // Should trigger NaN check
  assert(isnan(result3));

  // And -inf / -inf
  float result4 = (-INFINITY) / (-INFINITY); // Should trigger NaN check
  assert(isnan(result4));

  return 0;
}
