#include <assert.h>
#include <setjmp.h>

int main()
{
  _longjmp();
  assert(0);
  return 0;
}
