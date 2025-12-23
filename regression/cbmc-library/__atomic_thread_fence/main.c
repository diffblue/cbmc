#include <assert.h>

#ifndef __GNUC__
void __atomic_thread_fence(int);
#endif

int main()
{
  __atomic_thread_fence(0);
  assert(0);
  return 0;
}
