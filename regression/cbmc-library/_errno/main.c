#include <assert.h>
#include <errno.h>

int main()
{
  _errno();
  assert(0);
  return 0;
}
