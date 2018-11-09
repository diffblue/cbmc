#include <assert.h>
#include <errno.h>

int main()
{
  __errno_location();
  assert(0);
  return 0;
}
