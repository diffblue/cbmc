#include <setjmp.h>

static sigjmp_buf env;

int main()
{
  siglongjmp(env, 1);
  __CPROVER_assert(0, "unreachable");
  return 0;
}
