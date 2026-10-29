#include <assert.h>

#ifndef _WIN32
#  include <pwd.h>

int main(void)
{
  struct passwd *result = getpwuid(0);
  // POSIX.1-2017: getpwuid may return NULL.
  if(result != 0)
  {
    assert(result->pw_uid == 0);
  }
  // Assert it's always non-NULL: this must FAIL, proving the NULL
  // path is reachable.
  assert(result != 0);
  return 0;
}
#else
int main(void)
{
  return 0;
}
#endif
