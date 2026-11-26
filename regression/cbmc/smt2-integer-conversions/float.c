#include <float.h>

int main()
{
  __CPROVER_integer p = 1;
  for(int k = 0; k < 200; ++k)
    p *= 2;

  // nondeterministic, so that the conversions are not constant-folded
  __CPROVER_integer big;
  __CPROVER_assume(big > p - 1 && big < p + 1);

  float f = big;
  __CPROVER_assert(f == 1.0f / 0.0f, "2^200 rounds to infinity as float");
  double d = big;
  __CPROVER_assert(d == 0x1p200, "2^200 is exact as double");
  float g = -big;
  __CPROVER_assert(g == -1.0f / 0.0f, "-2^200 rounds to -infinity");

  __CPROVER_integer odd;
  __CPROVER_assume(odd > 16777216 && odd < 16777218);
  float h = odd;
  __CPROVER_assert(h == 16777216.0f, "ties to even");

  __CPROVER_rounding_mode = 3; // towards zero
  float z = big;
  __CPROVER_assert(z == FLT_MAX, "towards zero, 2^200 becomes FLT_MAX");
  float y = odd;
  __CPROVER_assert(y == 16777216.0f, "towards zero");

  __CPROVER_rounding_mode = 2; // upwards
  float u = odd;
  __CPROVER_assert(u == 16777218.0f, "upwards");
  __CPROVER_assert(u == 16777216.0f, "fails");
  return 0;
}
