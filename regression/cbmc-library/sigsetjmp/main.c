#include <setjmp.h>

static sigjmp_buf env;

int main()
{
  if(sigsetjmp(env, 0))
    __CPROVER_assert(0, "reached via siglongjmp");
  else
    __CPROVER_assert(0, "sigsetjmp called directly");
  return 0;
}
