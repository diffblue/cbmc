#include <assert.h>
#include <signal.h>

int main()
{
  kill();
  assert(0);
  return 0;
}
