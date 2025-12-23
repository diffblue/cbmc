#include <errno.h>
#include <unistd.h>

main()
{
  long result;
  int name;

  errno = 0;
  // Testing sysconf as an over-apporximation.
  // We expect to cover all branches, thus, all assertions should fail.
  if((result = sysconf(name)) == -1)
  {
    if(errno == 0)
    {
      __CPROVER_assert(0, "ARG_MAX is not supported");
    }
    else
    {
      __CPROVER_assert(0, "sysconf() error");
    }
  }
  else
  {
    __CPROVER_assert(0, "ARG_MAX is supported");
  }
}
