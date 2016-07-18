// race protected by wrong locks

#include <pthread.h>

pthread_mutex_t m1, m2;

int x;

void my_lock(pthread_mutex_t *mm)
{
  pthread_mutex_lock(mm);
}

void my_unlock(pthread_mutex_t *mm)
{
  pthread_mutex_unlock(mm);
}

void inc(int *z)
{
  (*z)++;
}

void *thr1(void *arg)
{
  int k=0;

  my_lock(&m1);
  inc(&x);
  my_unlock(&m1);

  while(k<10)
    k++;
}


void *thr2(void *arg)
{
  my_lock(&m2);
  ++x;
  pthread_mutex_t *p=&m2;

  my_unlock(p);
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
