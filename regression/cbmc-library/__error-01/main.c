#include <assert.h>
#include <errno.h>

int main()
{
  __error();
  assert(0);
  return 0;
}
