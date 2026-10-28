#include <assert.h>
#include <pthread.h>

// POSIX.1-2017: a thread may hold multiple concurrent read locks.
int main(void)
{
  pthread_rwlock_t l = PTHREAD_RWLOCK_INITIALIZER;
  int r1 = pthread_rwlock_rdlock(&l);
  int r2 = pthread_rwlock_rdlock(&l);
  assert(0); // reachable: both rdlocks succeed
  return 0;
}
