// accesses to x, y are concurrent

#include <pthread.h>

pthread_mutex_t lock1=PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock2=PTHREAD_MUTEX_INITIALIZER;

void *thread1(void *arg)
{
  int x;
  pthread_mutex_lock(&lock1);
  x = 1;
  pthread_mutex_unlock(&lock1);
}

void *thread2(void *arg)
{
  int y;
  pthread_mutex_lock(&lock2);
  y = 1;
  pthread_mutex_unlock(&lock2);
}

int main()
{
  pthread_t tid1;
  pthread_t tid2;

  pthread_create(&tid1, 0, thread1, 0);
  pthread_create(&tid2, 0, thread2, 0);

  return 0;
}

