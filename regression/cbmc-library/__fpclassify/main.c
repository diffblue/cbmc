#include <assert.h>
#include <float.h>
#include <math.h>

#ifdef __GNUC__
void inductiveStepHunt(float startState)
{
  float target = 0x1.fffffep-3f;

  __CPROVER_assume(
    (0 < startState) && (fpclassify(startState) == FP_NORMAL) &&
    (0x1p-126f <= startState));

  float secondPoint = (target / startState);

  float nextState = (startState + secondPoint) / 2;

  float oneAfter = (target / nextState);

  assert(oneAfter > 0);
}

void simplifiedInductiveStepHunt(float nextState)
{
  float target = 0x1.fffffep-3f;

  // Implies nextState == 0x1p+124f;
  __CPROVER_assume(
    (0x1.fffffep+123f < nextState) && (nextState < 0x1.000002p+124f));

  float oneAfter = (target / nextState);

  // Is true and correctly proven by constant evaluation
  // Note that this is the smallest normal number
  assert(0x1.fffffep-3f / 0x1p+124f == 0x1p-126f);

  assert(oneAfter > 0);
}
#endif

int main(void)
{
#ifdef __GNUC__
  //  inductiveStepHunt(0x1p+125f);
  //  simplifiedInductiveStepHunt(0x1p+124f);

  float f, g;

  inductiveStepHunt(f);
  simplifiedInductiveStepHunt(g);
#endif

// Visual Studio needs to be 2013 onwards
#if defined(_MSC_VER) && !defined(__CYGWIN__) && _MSC_VER < 1800

  // see http://www.johndcook.com/math_h.html

#else
  assert(fpclassify(DBL_MAX + DBL_MAX) == FP_INFINITE);
  assert(fpclassify(0 * (DBL_MAX + DBL_MAX)) == FP_NAN);
  assert(fpclassify(1.0) == FP_NORMAL);
  assert(fpclassify(DBL_MIN) == FP_NORMAL);
  assert(fpclassify(DBL_MIN / 2) == FP_SUBNORMAL);
  assert(fpclassify(-0.0) == FP_ZERO);
#endif

#if !defined(__clang__) && defined(__GNUC__)
  assert(__builtin_fpclassify(0, 1, 2, 3, 4, DBL_MAX + DBL_MAX) == 1);
  assert(__builtin_fpclassify(0, 1, 2, 3, 4, 0 * (DBL_MAX + DBL_MAX)) == 0);
  assert(__builtin_fpclassify(0, 1, 2, 3, 4, 1.0) == 2);
  assert(__builtin_fpclassify(0, 1, 2, 3, 4, DBL_MIN) == 2);
  assert(__builtin_fpclassify(0, 1, 2, 3, 4, DBL_MIN / 2) == 3);
  assert(__builtin_fpclassify(0, 1, 2, 3, 4, -0.0) == 4);

  // these are compile-time
  _Static_assert(
    __builtin_fpclassify(0, 1, 2, 3, 4, -0.0) == 4,
    "__builtin_fpclassify is constant");
#endif

  return 0;
}
