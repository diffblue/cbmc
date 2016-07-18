// accesses to x, y are concurrent

#include <pthread.h>

int x;
int y;

void *thread1(void *arg)
{
  x = 1;
  return 0;
}

void *thread2(void *arg)
{
  y = 1;
  return 0;
}

int main()
{
  pthread_t *tid1;
  pthread_t *tid2;

  pthread_create(&tid1, 0, thread1, 0);
  pthread_join(tid2, 0); // join with different thread id

  pthread_create(&tid2, 0, thread2, 0);

  return 0;
}

