#include <assert.h>

#ifndef _WIN32
#  include <pwd.h>

int main(void)
{
  const char *user = "user";
  struct passwd *result = getpwnam(user);
  // POSIX.1-2017: getpwnam may return NULL.
  if(result != 0)
  {
    // pw_name was set to the argument.
    assert(result->pw_name == user);
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
