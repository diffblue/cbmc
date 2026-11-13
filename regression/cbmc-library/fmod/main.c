// CBMC verifies exact IEEE 754 bit patterns, so equality with decimal
// literals is intentional: both sides are concrete IEEE 754 values.
#include <assert.h>
#include <math.h>

int main()
{
  // examples from
  // https://stackoverflow.com/questions/2947044/how-do-i-use-modulus-for-float-double
  // and
  // https://stackoverflow.com/questions/25734144/difference-between-c-functions-remainder-and-fmod
  // Note: 0.3 and 0.2 are not exactly representable in IEEE 754 double, but
  // the results are correct because fmod is computed exactly on the nearest
  // representable values.
  double d1 = fmod(0.5, 0.3);
  assert(d1 == 0.2);
  double d2 = fmod(-0.5, 0.3);
  assert(d2 == -0.2);
  // Same test using hex float literals for clarity:
  // 0.5 == 0x1.0p-1, 0.3 == 0x1.3333333333333p-2, 0.2 == 0x1.999999999999ap-3
  double d3 = fmod(0x1.0p-1, 0x1.3333333333333p-2);
  assert(d3 == 0x1.999999999999ap-3);
  double d4 = fmod(-0x1.0p-1, 0x1.3333333333333p-2);
  assert(d4 == -0x1.999999999999ap-3);
  double x = 7.5, y = 2.1;
  double xModY = fmod(x, y);
  assert(xModY > 1.19 && xModY < 1.21);
}
