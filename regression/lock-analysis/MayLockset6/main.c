#include <pthread.h>

pthread_mutex_t m;

void *thread(void *arg)
{
  pthread_mutex_lock(&m);

  return 0;
}

int main()
{
  pthread_t tid;

  pthread_create(&tid, 0, thread, 0);

  return 0;
}

