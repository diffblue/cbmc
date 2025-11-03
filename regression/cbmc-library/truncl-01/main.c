#include <assert.h>
#include <math.h>

int main()
{
  assert(truncl(1.1l) == 1.0l);
  assert(truncl(1.9l) == 1.0l);
  assert(truncl(-1.1l) == -1.0l);
  assert(truncl(-1.9l) == -1.0l);

#if !defined(__APPLE__) || __ENVIRONMENT_OS_VERSION_MIN_REQUIRED__ >= 160000
  assert(signbit(truncl(-0.0l)));
#endif

  return 0;
}
