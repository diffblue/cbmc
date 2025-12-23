#include <assert.h>
#include <unistd.h>

int main()
{
  _write();
  assert(0);
  return 0;
}
