#include <assert.h>
#include <setjmp.h>

int main()
{
  setjmp();
  assert(0);
  return 0;
}
