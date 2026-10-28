#include <assert.h>
#include <pthread.h>

pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t c = PTHREAD_COND_INITIALIZER;
int x = 0;

void *t(void *a)
{
  (void)a;
  pthread_mutex_lock(&m);
  x = 1;
  pthread_cond_signal(&c);
  pthread_mutex_unlock(&m);
  return 0;
}

// POSIX.1-2017 pthread_cond_wait: the mutex is released while waiting,
// so the other thread can take it and set x=1.  The assertion x==0 can
// therefore fail and CBMC must report it.
int main(void)
{
  pthread_t th;
  pthread_mutex_lock(&m);
  pthread_create(&th, 0, t, 0);
  pthread_cond_wait(&c, &m);
  assert(x == 0);
  pthread_mutex_unlock(&m);
  pthread_join(th, 0);
  return 0;
}
