#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_barrier_destroy();
  assert(0);
  return 0;
}
