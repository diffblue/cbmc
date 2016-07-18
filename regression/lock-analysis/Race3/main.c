// race: i could be 1

#include <pthread.h>

pthread_mutex_t m;

int x[10];

void *thr1(void *arg)
{
  unsigned i;
  x[i]=1;
}


void *thr2(void *arg)
{
  x[1]=2;
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
