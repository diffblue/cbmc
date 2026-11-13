#include <assert.h>
#include <threads.h>

// C17 7.26.2.1: call_once calls func exactly once.
static int flag = 0;
static void f(void)
{
  flag = 1;
}

int main(void)
{
  once_flag of = ONCE_FLAG_INIT;
  call_once(&of, f);
  // f was called: flag must be 1, so this assertion must FAIL.
  assert(flag == 0);
  return 0;
}
