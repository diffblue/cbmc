// no race protected by locks

#include <pthread.h>

int x;

void *thr1(void *arg)
{
  ++x;
}




int main()
{
	pthread_t tid1, tid2;
  pthread_create(&tid1, NULL, thr1, NULL);
  pthread_join(tid1, NULL);

  return 0;
}
