#include <assert.h>
#include <fenv.h>
#include <float.h>
#include <math.h>

float nondet_float(void);
double nondet_double(void);
long double nondet_long_double(void);

int main(void)
{
  // symbolic arguments: the square root is computed by the solver
  float f = nondet_float();
  __CPROVER_assume(f == 2.0f);
  double d = nondet_double();
  __CPROVER_assume(d == 1.0 + DBL_EPSILON);
  long double l = nondet_long_double();
  __CPROVER_assume(l == 4.0L);

  assert(sqrtf(f) == 0x1.6a09e6p+0f);
  assert(sqrt(d) == 1.0);
  assert(sqrtl(l) == 2.0L);

  fesetround(FE_UPWARD);
  assert(sqrtf(f) == 0x1.6a09e8p+0f);
  assert(sqrt(d) == 0x1.0000000000001p+0);
  fesetround(FE_DOWNWARD);
  assert(sqrt(d) == 1.0);

  // special values
  float x = nondet_float();
  __CPROVER_assume(x < 0);
  assert(isnan(sqrtf(x)));
  assert(signbit(sqrt(-0.0)));
  assert(isinf(sqrt(d * 0 + INFINITY)));

  return 0;
}
