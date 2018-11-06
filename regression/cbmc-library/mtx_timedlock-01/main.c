#include <assert.h>
#include <threads.h>

int main()
{
  mtx_timedlock();
  assert(0);
  return 0;
}
