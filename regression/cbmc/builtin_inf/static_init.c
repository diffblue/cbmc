#include <assert.h>
#include <math.h>

float g = -INFINITY;

void test_static_float_infinity()
{
  static float f = +INFINITY;
  assert(isinf(f));
}

void test_static_double_infinity()
{
  static double d = INFINITY;
  assert(isinf(d));
}

void test_static_long_double_infinity()
{
  static long double ld = INFINITY;
  assert(isinf(ld));
}

void test_static_huge_val()
{
  static float f = HUGE_VALF;
  static double d = HUGE_VAL;
  static long double ld = HUGE_VALL;

  assert(isinf(f));
  assert(isinf(d));
  assert(isinf(ld));
}

int main()
{
  test_static_float_infinity();
  test_static_double_infinity();
  test_static_long_double_infinity();
  test_static_huge_val();
  return 0;
}
