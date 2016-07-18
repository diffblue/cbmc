// race protected by wrong locks

#include <pthread.h>

pthread_mutex_t m1, m2;

int x;

void inc(int *z)
{
  (*z)++;
}

void *thr1(void *arg)
{
  int k=0;

  pthread_mutex_lock(&m1);
  inc(&x);
  pthread_mutex_unlock(&m1);

  while(k<10)
    k++;
}


void *thr2(void *arg)
{
  pthread_mutex_lock(&m2);
  ++x;
  pthread_mutex_t *p=&m2;

  pthread_mutex_unlock(p);
}


int main()
{
  pthread_t tid1, tid2;
  pthread_create(&tid1, NULL, thr1, NULL);
  pthread_create(&tid2, NULL, thr2, NULL);

  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);

  return 0;
}
