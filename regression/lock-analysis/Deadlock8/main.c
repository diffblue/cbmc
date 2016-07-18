// no deadlock

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

  int k=0;

  pthread_mutex_lock(&m2);
  pthread_mutex_lock(&m1);
  ++x;
  pthread_mutex_unlock(&m1);
  pthread_mutex_unlock(&m2);
}

int main()
{
  pthread_t tid1, tid2;
  pthread_create(&tid1, NULL, thr, NULL);

  pthread_join(tid1, NULL);

  return 0;
}
