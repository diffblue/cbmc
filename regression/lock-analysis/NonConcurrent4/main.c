// accesses to x, y are non-concurrent

#include <pthread.h>

int x;

void *thread1(void *arg)
{
  x = 1;
}

void *thread2(void *arg)
{
  x = 2;
}

int main()
{
  pthread_t tid1;
  pthread_t tid2;

  if (x)
  {
    pthread_create(&tid1, 0, thread1, 0);
  }
  else
  {
    pthread_create(&tid2, 0, thread2, 0);
  }

  return 0;
}

