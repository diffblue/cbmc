#include <assert.h>
#include <math.h>

int main()
{
  assert(floorl(1.1l) == 1.0l);
  assert(floorl(1.9l) == 1.0l);
  assert(floorl(-1.1l) == -2.0l);
  assert(floorl(-1.9l) == -2.0l);

#if !defined(__APPLE__) || __ENVIRONMENT_OS_VERSION_MIN_REQUIRED__ >= 160000
  assert(signbit(floorl(-0.0l)));
#endif

  return 0;
}
