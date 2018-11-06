#include <assert.h>
#include <unistd.h>

int main()
{
  _close();
  assert(0);
  return 0;
}
