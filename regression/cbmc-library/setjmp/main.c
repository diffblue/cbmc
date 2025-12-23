#include <setjmp.h>

static jmp_buf env;

int main()
{
  if(setjmp(env))
    __CPROVER_assert(0, "reached via longjmp");
  else
    __CPROVER_assert(0, "setjmp called directly");
  return 0;
}
