#ifdef __GNUC__
#include <assert.h>
#include <fenv.h>

float nondet_float();
int nondet_int();

float castWithRounding(int rounding_mode, int value)
{
  int returnValue = fesetround(rounding_mode);

  assert(returnValue == 0);

  return (float)value;
}
#endif

int main(void)
{
#ifdef __GNUC__
  float low = 0x1p+25f;           // 33554432
  float high = 0x1.000002p+25f;   // 33554436
  float higher = 0x1.000004p+25f; // 33554440

  // There are no other floating point numbers between these
  float other = nondet_float();
  assert(!((low < other) && (other < high)));

  // Inference tests
  int x = nondet_int();

  // x is 33554433, 33554434 or 33554435
  __CPROVER_assume((33554432 < x) && (x < 33554436));

  assert((castWithRounding(FE_TONEAREST, x) == high) == (x == 33554435));

#ifdef FE_UPWARD
  assert(castWithRounding(FE_UPWARD, x) == high);
  assert(castWithRounding(FE_UPWARD, -x) == -low);
#endif

#ifdef FE_DOWNWARD
  assert(castWithRounding(FE_DOWNWARD, x) == low);
  assert(castWithRounding(FE_DOWNWARD, -x) == -high);
#endif

  assert(castWithRounding(FE_TOWARDZERO, x) == low);
  assert(castWithRounding(FE_TOWARDZERO, -x) == -low);
#endif
}
