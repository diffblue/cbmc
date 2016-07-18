#include <pthread.h>

//Race on NULL object?
//#define YES

#ifndef YES
int x;
#endif
int * gp
#ifndef YES
= &x
#endif
;

void * thr1 (void *pram)
{
  *gp = 0;
  return 0;
}

void * thr2 (void *pram)
{
  *gp = 1;
  return 0;
}

int main ()
{
  pthread_t tid1,tid2;
  pthread_create(&tid1, 0, thr1, 0);
  pthread_create(&tid2, 0, thr2, 0);
  pthread_join(tid1, 0);
  pthread_join(tid1, 0);
  return 0;
}
