#include <pthread.h>

typedef struct
{
  pthread_mutex_t *m1;
  pthread_mutex_t *m2;
} st_t;

int main()
{
  pthread_mutex_t m1;
  pthread_mutex_t m2;
  pthread_mutex_t *p1;

  p1 = &m1;

  pthread_mutex_lock(p1);
  pthread_mutex_unlock(p1);

  pthread_mutex_t **p2;
  pthread_mutex_t **p3;

  p2 = &p1;

  p3 = p2; // after this we can modify the value of p1 via p3
  *p3 = &m2;

  st_t s;
  s.m1 = &m1;
  s.m2 = &m2;

  st_t *sp;
  sp = &s;

  return 0;
}

