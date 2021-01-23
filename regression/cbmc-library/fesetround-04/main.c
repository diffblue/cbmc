#ifdef __GNUC__

#include <assert.h>
#include <fenv.h>

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

  // Constant folding tests
  assert(castWithRounding(FE_TONEAREST, 33554432) == low);
  assert(castWithRounding(FE_TONEAREST, 33554433) == low);
  assert(castWithRounding(FE_TONEAREST, 33554434) == low); // Even is low
  assert(castWithRounding(FE_TONEAREST, 33554435) == high);
  assert(castWithRounding(FE_TONEAREST, 33554436) == high);
  assert(castWithRounding(FE_TONEAREST, 33554437) == high);
  assert(castWithRounding(FE_TONEAREST, 33554438) == higher); // Even is high
  assert(castWithRounding(FE_TONEAREST, 33554439) == higher);
  assert(castWithRounding(FE_TONEAREST, 33554440) == higher);

#ifdef FE_UPWARD
  assert(castWithRounding(FE_UPWARD, 33554432) == low);
  assert(castWithRounding(FE_UPWARD, 33554433) == high);
  assert(castWithRounding(FE_UPWARD, 33554434) == high);
  assert(castWithRounding(FE_UPWARD, 33554435) == high);
  assert(castWithRounding(FE_UPWARD, 33554436) == high);
  assert(castWithRounding(FE_UPWARD, -33554432) == -low);
  assert(castWithRounding(FE_UPWARD, -33554433) == -low);
  assert(castWithRounding(FE_UPWARD, -33554434) == -low);
  assert(castWithRounding(FE_UPWARD, -33554435) == -low);
  assert(castWithRounding(FE_UPWARD, -33554436) == -high);
#endif

#ifdef FE_DOWNWARD
  assert(castWithRounding(FE_DOWNWARD, 33554432) == low);
  assert(castWithRounding(FE_DOWNWARD, 33554433) == low);
  assert(castWithRounding(FE_DOWNWARD, 33554434) == low);
  assert(castWithRounding(FE_DOWNWARD, 33554435) == low);
  assert(castWithRounding(FE_DOWNWARD, 33554436) == high);
  assert(castWithRounding(FE_DOWNWARD, -33554432) == -low);
  assert(castWithRounding(FE_DOWNWARD, -33554433) == -high);
  assert(castWithRounding(FE_DOWNWARD, -33554434) == -high);
  assert(castWithRounding(FE_DOWNWARD, -33554435) == -high);
  assert(castWithRounding(FE_DOWNWARD, -33554436) == -high);
#endif

  assert(castWithRounding(FE_TOWARDZERO, 33554432) == low);
  assert(castWithRounding(FE_TOWARDZERO, 33554433) == low);
  assert(castWithRounding(FE_TOWARDZERO, 33554434) == low);
  assert(castWithRounding(FE_TOWARDZERO, 33554435) == low);
  assert(castWithRounding(FE_TOWARDZERO, 33554436) == high);
  assert(castWithRounding(FE_TOWARDZERO, -33554432) == -low);
  assert(castWithRounding(FE_TOWARDZERO, -33554433) == -low);
  assert(castWithRounding(FE_TOWARDZERO, -33554434) == -low);
  assert(castWithRounding(FE_TOWARDZERO, -33554435) == -low);
  assert(castWithRounding(FE_TOWARDZERO, -33554436) == -high);
#endif
}
