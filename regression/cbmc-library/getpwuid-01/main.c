#include <assert.h>

#ifndef _WIN32
#  include <pwd.h>

int main()
{
  struct passwd *result = getpwuid(0);
  (void)*result;
  return 0;
}
#else
int main()
{
}
#endif
