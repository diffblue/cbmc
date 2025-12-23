#include <assert.h>
#include <threads.h>

int main()
{
  mtx_lock();
  assert(0);
  return 0;
}
