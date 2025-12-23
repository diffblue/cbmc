#include <assert.h>
#include <unistd.h>

int main()
{
  unlink();
  assert(0);
  return 0;
}
