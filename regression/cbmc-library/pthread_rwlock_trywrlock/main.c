#include <assert.h>
#include <errno.h>
#include <pthread.h>

// POSIX.1-2017: trywrlock returns EBUSY when locked.
int main(void)
{
  pthread_rwlock_t l = PTHREAD_RWLOCK_INITIALIZER;
  pthread_rwlock_wrlock(&l);
  int r = pthread_rwlock_trywrlock(&l);
  assert(r == EBUSY);
  return 0;
}
