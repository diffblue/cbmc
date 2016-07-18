#include <pthread.h>

pthread_mutex_t m1;
pthread_mutex_t m2;

void func(pthread_mutex_t *mutex)
{
  *mutex = m2;
}

int main()
{
  func(&m1);

  pthread_mutex_lock(&m1);
  pthread_mutex_unlock(&m1);

  return 0;
}

