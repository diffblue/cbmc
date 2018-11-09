#include <assert.h>
#include <fenv.h>

int main()
{
  fegetround();
  assert(0);
  return 0;
}
