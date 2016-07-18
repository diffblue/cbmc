// accesses to x, y are concurrent

#include <pthread.h>

int x;
int *px;
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

void *thread3(void *arg)
{
  y = 2;
  return 0;
}

int main()
{
  px = &x;

  pthread_t tid1;
  pthread_t tid2;
  pthread_t tid3;

  x = 34;

  pthread_create(&tid1, 0, thread1, 0);
  pthread_create(&tid2, 0, thread2, 0);
  pthread_join(tid2, 0); // join with different thread id

  x = 35;
  pthread_create(&tid3, 0, thread3, 0);
  pthread_join(tid3, 0);

  return 0;
}

