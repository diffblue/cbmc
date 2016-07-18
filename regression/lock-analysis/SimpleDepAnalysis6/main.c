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
  pthread_t tid;

  int i;

  pthread_create(&tid, 0, func1, (void *)i);

  pthread_mutex_lock(&m);

  i = (int)&m;

  return 0;
}

