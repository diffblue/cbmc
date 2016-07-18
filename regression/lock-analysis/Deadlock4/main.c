// Example by Havelund et al 2010
// deadlock possible

#include <pthread.h>

pthread_mutex_t m1,m2,m3,m4;

int x;

void *thr1(void *arg)
{
  pthread_mutex_lock(&m1);
  pthread_mutex_lock(&m2);
  ++x;
  pthread_mutex_unlock(&m2);
  pthread_mutex_unlock(&m1);

  int k=0;

  pthread_mutex_lock(&m3);
  pthread_mutex_lock(&m4);
  ++x;
  pthread_mutex_unlock(&m4);
  pthread_mutex_unlock(&m3);
}


void *thr2(void *arg)
{
  pthread_mutex_lock(&m2);
  pthread_mutex_lock(&m3);
  ++x;
  pthread_mutex_unlock(&m3);
  pthread_mutex_unlock(&m2);
}

void *thr3(void *arg)
{
  pthread_mutex_lock(&m4);
  pthread_mutex_lock(&m1);
  ++x;
  pthread_mutex_unlock(&m1);
  pthread_mutex_unlock(&m4);
}

void *thr4(void *arg)
{
  pthread_mutex_lock(&m4);
  pthread_mutex_lock(&m3);
  ++x;
  pthread_mutex_unlock(&m3);
  pthread_mutex_unlock(&m4);
}


int main()
{
  pthread_t tid1, tid2, tid3, tid4;
  pthread_create(&tid1, NULL, thr1, NULL);
  pthread_create(&tid2, NULL, thr2, NULL);
  pthread_create(&tid3, NULL, thr3, NULL);
  pthread_create(&tid4, NULL, thr4, NULL);

  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  pthread_join(tid3, NULL);
  pthread_join(tid4, NULL);

  return 0;
}
