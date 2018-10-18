#include <assert.h>
#include <math.h>

#ifndef _MSC_VER
#include <fenv.h>
#endif

void testAdd(int mode, double f, double g, int sign)
{
#ifndef _MSC_VER
  int error = fesetround(mode);
  assert(error == 0);

  double f_plus_g = f + g;
  double g_plus_f = g + f;

  assert(f_plus_g == 0.0);
  assert(g_plus_f == 0.0);

  assert(signbit(f_plus_g) == sign);
  assert(signbit(g_plus_f) == sign);
#endif

  return;
}

int main(int argc, char **argv)
{
#ifndef _MSC_VER
  double plusZero = 0.0;
  assert(signbit(plusZero) == 0);

  double minusZero = -0.0;
  assert(signbit(minusZero) == 1);

  double var = 0x1.73b7985271bcep+4;

  testAdd(FE_TONEAREST, plusZero, plusZero, 0);
  testAdd(FE_TONEAREST, minusZero, minusZero, 1);
  testAdd(FE_TONEAREST, plusZero, minusZero, 0);
  testAdd(FE_TONEAREST, var, -var, 0);

#ifdef FE_UPWARD
  testAdd(FE_UPWARD, plusZero, plusZero, 0);
  testAdd(FE_UPWARD, minusZero, minusZero, 1);
  testAdd(FE_UPWARD, plusZero, minusZero, 0);
  testAdd(FE_UPWARD, var, -var, 0);
#endif

#ifdef FE_DOWNWARD
  testAdd(FE_DOWNWARD, plusZero, plusZero, 0);
  testAdd(FE_DOWNWARD, minusZero, minusZero, 1);
  testAdd(FE_DOWNWARD, plusZero, minusZero, 1);
  testAdd(FE_DOWNWARD, var, -var, 1);
#endif

  testAdd(FE_TOWARDZERO, plusZero, plusZero, 0);
  testAdd(FE_TOWARDZERO, minusZero, minusZero, 1);
  testAdd(FE_TOWARDZERO, plusZero, minusZero, 0);
  testAdd(FE_TOWARDZERO, var, -var, 0);
#endif

  return 0;
}
