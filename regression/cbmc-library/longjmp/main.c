#include <setjmp.h>

static jmp_buf env;

int main()
{
  longjmp(env, 1);
  __CPROVER_assert(0, "unreachable");
  return 0;
}
