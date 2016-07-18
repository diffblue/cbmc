#include <pthread.h>

int main()
{
  pthread_mutex_t m;
  pthread_mutex_lock(&m);
  pthread_mutex_unlock(&m);

  int x;
  int y;
  int z;

  int a[10];
  int i;
  int j;

  void *p;

  i = 0;
  x = y + *(&z);
  x = a[i];

  p = (void *)&m;
  j = (int)p;
  j = 1;

  return 0;
}

