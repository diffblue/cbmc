#include <assert.h>

int main()
{
  __atomic_thread_fence(0);
  assert(0);
  return 0;
}
