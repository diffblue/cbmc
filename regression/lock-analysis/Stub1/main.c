//#include <pthread.h>
#include "pthread_.h"

int x;

void * thr1 (void * arg)
{
  x = 0;                     // expect: 1586
  return 0;
}


void *thr2 (void * arg)
{
  x = 1;                     // expect: 1586
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
