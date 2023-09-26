#include <assert.h>

#ifndef _WIN32
#  include <pwd.h>

int main()
{
  const char *user = "user";
  struct passwd *result = getpwnam(user);
  (void)*result;
  return 0;
}
#else
int main()
{
}
#endif
