#include <assert.h>
#include <threads.h>

int main()
{
  mtx_unlock();
  assert(0);
  return 0;
}
