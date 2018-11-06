#include <assert.h>
#include <setjmp.h>

int main()
{
  siglongjmp();
  assert(0);
  return 0;
}
