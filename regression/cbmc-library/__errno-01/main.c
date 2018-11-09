#include <assert.h>
#include <errno.h>

int main()
{
  __errno();
  assert(0);
  return 0;
}
