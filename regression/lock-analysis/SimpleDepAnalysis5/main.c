#include <pthread.h>

int func(int a, int b)
{
  if (a) {
    return b + 1;
  } else {
    return b + 2;
  }
}


int main()
{
  pthread_mutex_t m;

  pthread_mutex_lock(&m);
  pthread_mutex_unlock(&m);

  pthread_mutex_t *mp;  

  mp = &m; // +

  int *ip;
  ip = (int *)mp; // +

  ip = func(1, 2);

  return 0;
}

