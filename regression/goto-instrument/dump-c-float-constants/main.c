#include <assert.h>
#include <stdint.h>

union float_bits
{
  float f;
  uint32_t u;
};

union double_bits
{
  double d;
  uint64_t u;
};

int main(void)
{
  // Constants that the printf-style "%g" format (6 significant digits) does
  // not represent exactly; --dump-c must print them such that they are read
  // back as the same value.
  union float_bits f;
  f.f = 0x1p-46f;
  assert(f.u == 0x28800000u);
  f.f = 0x1.921fb6p+1f; // pi rounded to float
  assert(f.u == 0x40490fdbu);
  f.f = -0x1.99999ap-4f; // -0.1f
  assert(f.u == 0xbdcccccdu);

  union double_bits d;
  d.d = 0x1.0000000000001p+0; // 1 + 2^-52
  assert(d.u == 0x3ff0000000000001ull);
  d.d = 0x1.fffffffffffffp+1023; // DBL_MAX
  assert(d.u == 0x7fefffffffffffffull);
  d.d = 0x0.0000000000001p-1022; // smallest subnormal
  assert(d.u == 1ull);
  d.d = 0.1;
  assert(d.u == 0x3fb999999999999aull);

  // constants that %g does represent exactly are printed as before
  d.d = 0.5;
  assert(d.u == 0x3fe0000000000000ull);

  return 0;
}
