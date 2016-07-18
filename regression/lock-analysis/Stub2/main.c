//for testing what happens if lock handles are integers

#include "pthread_.h"

int x;
pthread_mutex_t m1=1, m2=2;

void * thr1 (void * arg)
{
  arg = arg;
  pthread_mutex_lock(m1,0);
  pthread_mutex_lock(m2,0);
  x = 0;                     
  pthread_mutex_unlock(m2);
  pthread_mutex_unlock(m1);
  return 0;
}

void *thr2 (void * arg)
{
  pthread_mutex_lock(m2,0);
  pthread_mutex_lock(m1,0);
  x = 1;                     
  pthread_mutex_unlock(m1);
  pthread_mutex_unlock(m2);
  return 0;
}

int main (void)
{
  pthread_t tid1, tid2;
  pthread_create(&tid1, 0, &thr1, 0);
  pthread_create(&tid2, 0, &thr2, 0);

  pthread_join(tid1, 0);
  pthread_join(tid2, 0);

  return x;
}
