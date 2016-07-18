#include <pthread.h>

pthread_mutex_t m;

void func1()
{
  func2();
}

void func2()
{
  func3();
}

void func3()
{
  int i;

  i = (int)&m;
}

int main()
{
  pthread_mutex_lock(&m);

  func1();

  return 0;
}

