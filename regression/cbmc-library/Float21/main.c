/*
** subnormal-boundary.c
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 25/07/12
**
** Regression tests for casting and classification around the subnormal boundary.
**
*/

#include <assert.h>
#include <math.h>

float nondet_float(void);

int main(void)
{
#ifdef __GNUC__

  float smallestNormalFloat = 0x1.0p-126f;
  float largestSubnormalFloat = 0x1.fffffcp-127f;

  double v = 0x1.FFFFFFp-127;

  float f;

  // Check the encodings are correct
  assert(fpclassify(largestSubnormalFloat) == FP_SUBNORMAL);

  f = nondet_float();
  __CPROVER_assume(fpclassify(f) == FP_SUBNORMAL);
  assert(f <= largestSubnormalFloat);

  assert(fpclassify(smallestNormalFloat) == FP_NORMAL);

  f = nondet_float();
  __CPROVER_assume(fpclassify(f) == FP_NORMAL);
  assert(smallestNormalFloat <= fabs(f));

  assert(largestSubnormalFloat < smallestNormalFloat);

  // Check the ordering as doubles
  assert(((double)largestSubnormalFloat) < ((double)smallestNormalFloat));
  assert(((double)largestSubnormalFloat) < v);
  assert(v < ((double)smallestNormalFloat));

  // Check coercion to float
  assert((float)((double)largestSubnormalFloat) == largestSubnormalFloat);
  assert((float)((double)smallestNormalFloat) == smallestNormalFloat);

  assert(
    ((double)smallestNormalFloat) - v <= v - ((double)largestSubnormalFloat));
  assert(((float)v) == smallestNormalFloat);

  f = nondet_float();
  __CPROVER_assume(fpclassify(f) == FP_SUBNORMAL);
  assert(((float)((double)f)) == f);

#endif

  return 0;
}
