#include <pthread.h>

pthread_mutex_t m;

void *func1(void *arg)
{
  int j;
  j = (int)arg;
}

void *func2(void *arg)
{
  int k;
  k = (int)arg;
}

int main()
{
  pthread_mutex_lock(&m);

  pthread_t tid;

  int i;
  i = (int)&m;

  pthread_create(&tid, 0, func1, (void *)i);

  return 0;
}

