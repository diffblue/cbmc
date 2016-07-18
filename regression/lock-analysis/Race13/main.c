#include <pthread.h>

int x;

void * thr1 (void * arg)
{
  x = 1;
  return 0;
}

int main (void)
{
	pthread_t tid1;
  pthread_create(&tid1, 0, &thr1, 0);

  x = 0;

  pthread_join(tid1, 0);

  return x;
}
