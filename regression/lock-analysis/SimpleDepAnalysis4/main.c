#include <pthread.h>

void func(int a, int b);

void func2(int a, int b)
{

}

void func3(int a, int b)
{
  a = b; // +
}

int main()
{
  pthread_mutex_t m;

  pthread_mutex_lock(&m);
  pthread_mutex_unlock(&m);

  int i;
  i = 0;

  func(i, (int)&m);

  int j;
  j = 0;

  func2(j, (int)&m);

  int k;
  k = 0; // +

  func3(k, (int)&m);

  return 0;
}

