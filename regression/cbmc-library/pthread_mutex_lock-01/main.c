#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_mutex_lock();
  assert(0);
  return 0;
}
