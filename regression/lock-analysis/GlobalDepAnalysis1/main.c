#include <pthread.h>

int main()
{
  pthread_mutex_t m;
  pthread_mutex_lock(&m);
  pthread_mutex_unlock(&m);

  void *p;
  int j;

  p = (void *)&m;
  j = (int)p;

  return 0;
}

