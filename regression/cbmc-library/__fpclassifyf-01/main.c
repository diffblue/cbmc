/*
** largestSubnormalFloat.c
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 25/07/12
**
*/

#include <assert.h>
#include <math.h>

int main(void)
{
#ifdef __GNUC__
  // Visual Studio won't parse the hexadecimal floating-point literal
  float largestSubnormalFloat = 0x1.fffffcp-127f;

  assert(fpclassify(largestSubnormalFloat) != FP_NAN);
  assert(fpclassify(largestSubnormalFloat) != FP_INFINITE);
  assert(fpclassify(largestSubnormalFloat) != FP_ZERO);
  assert(fpclassify(largestSubnormalFloat) != FP_NORMAL);
  assert(fpclassify(largestSubnormalFloat) == FP_SUBNORMAL);

  assert(__fpclassifyf(largestSubnormalFloat) == FP_SUBNORMAL);

  char b = __CPROVER_isnormalf(largestSubnormalFloat);

  assert(!b);
#endif

  return 0;
}
