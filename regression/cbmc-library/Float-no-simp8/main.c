#include <assert.h>
#include <math.h>

int main(int argc, char **argv)
{
  float f = -0x1p-129f;
  float g = 0x1p-129f;
  float target = 0x0;

  float result = f + g;

  assert(result == target);

#ifndef _MSC_VER
  assert(signbit(result) == signbit(target));
#endif

  return 0;
}
