#include <assert.h>
#include <pthread.h>

// POSIX.1-2017: wrlock then unlock is valid.
int main(void)
{
  pthread_rwlock_t l = PTHREAD_RWLOCK_INITIALIZER;
  pthread_rwlock_wrlock(&l);
  int r = pthread_rwlock_unlock(&l);
  assert(r == 0);
  return 0;
}
