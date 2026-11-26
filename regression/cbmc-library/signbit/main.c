#include <assert.h>
#include <math.h>

int main(int argc, char **argv)
{
  assert(signbit(-1.0) != 0);
  assert(signbit(1.0) == 0);
#if !defined(__APPLE__) || __ENVIRONMENT_OS_VERSION_MIN_REQUIRED__ >= 150000
  assert(signbit(-1.0l) != 0);
#endif
  assert(signbit(1.0l) == 0);

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
