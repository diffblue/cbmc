#include <assert.h>
#include <noop.h>

int main()
{
  __noop();
  assert(0);
  return 0;
}
