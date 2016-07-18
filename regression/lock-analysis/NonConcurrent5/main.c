// accesses to x, y are non-concurrent

#include <pthread.h>

int x;
int y;

void *thread(void *arg)
{
  y = 1;
}

int main()
{
  pthread_t tid;

  x = 1;
  pthread_create(&tid, 0, thread, 0);

  return 0;
}

