// accesses to x, y are non-concurrent

#include <pthread.h>

int x;
int y;

void *thread(void *arg)
{
  y = 1;
}

void func2()
{
  x = 1;
}

void func1()
{
  func2();
}

int main()
{
  pthread_t tid;

  func1();
  pthread_create(&tid, 0, thread, 0);

  return 0;
}

