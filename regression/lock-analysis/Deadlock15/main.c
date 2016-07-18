// deadlock

#include <pthread.h>

pthread_mutex_t m1,m2;

int x;

void *thr(void *arg)
{
  pthread_mutex_lock(&m1);
  pthread_mutex_lock(&m2);
  ++x;
  pthread_mutex_unlock(&m2);
  pthread_mutex_unlock(&m1);
}

void spawn(pthread_t *tid)
{
  pthread_create(&tid, NULL, thr, NULL);
}

int main()
{
  pthread_t tid;
  spawn(&tid);

  pthread_mutex_lock(&m2);
  pthread_mutex_lock(&m1);
  ++x;
  pthread_mutex_unlock(&m1);
  pthread_mutex_unlock(&m2);

  pthread_join(&tid, NULL);

  return 0;
}
