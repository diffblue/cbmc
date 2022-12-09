#include <setjmp.h>

#ifndef __GNUC__
#  define _longjmp(a, b) longjmp(a, b)
#endif

static jmp_buf env;

int main()
{
  _longjmp(env, 1);
  __CPROVER_assert(0, "unreachable");
  return 0;
}
