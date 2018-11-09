#include <assert.h>
#include <setjmp.h>

int main()
{
  longjmp();
  assert(0);
  return 0;
}
