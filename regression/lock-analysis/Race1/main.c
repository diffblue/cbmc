// no race protected by locks

#include <pthread.h>

pthread_mutex_t m;

int x;

void *thr1(void *arg)
{
  pthread_mutex_lock(&m);
  ++x;
  pthread_mutex_unlock(&m);

  int k=0;
}


void *thr2(void *arg)
{
  pthread_mutex_lock(&m);
  ++x;
  pthread_mutex_t *p=&m;

  pthread_mutex_unlock(&m);
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
