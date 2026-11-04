#include <assert.h>
#include <errno.h>
#include <pthread.h>

// POSIX.1-2017: tryrdlock returns EBUSY when write-locked.
int main(void)
{
  pthread_rwlock_t l = PTHREAD_RWLOCK_INITIALIZER;
  pthread_rwlock_wrlock(&l);
  int r = pthread_rwlock_tryrdlock(&l);
  assert(r == EBUSY);
  return 0;
}
