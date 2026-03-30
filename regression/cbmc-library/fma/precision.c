#include <assert.h>
#include <math.h>

int main()
{
  // Basic FMA
  assert(fmaf(2.0f, 3.0f, 4.0f) == 10.0f);
  assert(fmaf(-3.0f, 2.0f, 10.0f) == 4.0f);

  // FMA vs mul+add: FMA preserves precision lost by separate mul+add.
  // 0x1.fffffep+23 * 0x1.000002p+0 + 1.0:
  // mul rounds product to 0x1p+24, then +1 = 0x1p+24 (unchanged)
  // FMA keeps exact product, +1 = 0x1.000002p+24
  assert(0x1.fffffep+23f * 0x1.000002p+0f + 1.0f == 0x1p+24f);
  assert(fmaf(0x1.fffffep+23f, 0x1.000002p+0f, 1.0f) == 0x1.000002p+24f);

  // FMA for remainder: fma(-n, y, x) computes x - n*y with single rounding
  float x = 0x1.d55556p+0f;
  float y = 0x1.555556p-2f;
  assert(x - 5.0f * y == 0x1.55555p-3f);       // mul+sub: two roundings
  assert(fmaf(-5.0f, y, x) == 0x1.555554p-3f); // FMA: one rounding
}
