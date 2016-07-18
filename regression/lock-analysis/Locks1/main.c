// no race protected by locks

#include <pthread.h>

pthread_mutex_t m;

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

  my_lock(&m);
  inc(&x);
  my_unlock(&m);

  while(k<10)
    k++;
}


void *thr2(void *arg)
{
  my_lock(&m);
  ++x;
  pthread_mutex_t *p=&m;

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
