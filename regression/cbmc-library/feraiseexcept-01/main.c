#include <assert.h>
#include <fenv.h>

int main()
{
  int exceptions;
  feraiseexcept(exceptions);
  return 0;
}
