#include <assert.h>
#include <errno.h>
#include <pthread.h>

// POSIX.1-2017: trylock returns EBUSY when the mutex is already locked.
int main(void)
{
  pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
  pthread_mutex_lock(&m);
  int r = pthread_mutex_trylock(&m);
  assert(r == EBUSY);
  return 0;
}
