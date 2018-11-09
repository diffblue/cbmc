#include <assert.h>
#include <errno.h>

int main()
{
  ___errno();
  assert(0);
  return 0;
}
