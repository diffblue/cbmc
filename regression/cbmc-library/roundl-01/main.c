#include <assert.h>
#include <math.h>

int main()
{
  assert(roundl(1.1l) == 1.0l);
  assert(roundl(1.5l) == 2.0l);
  assert(roundl(1.9l) == 2.0l);
  assert(roundl(-1.1l) == -1.0l);
  assert(roundl(-1.5l) == -2.0l);
  assert(roundl(-1.9l) == -2.0l);

#if !defined(__APPLE__) || __ENVIRONMENT_OS_VERSION_MIN_REQUIRED__ >= 160000
  assert(signbit(roundl(-0.0l)));
#endif

  return 0;
}
