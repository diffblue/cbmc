#include <assert.h>
#ifdef __GNUC__
#include <pthread.h>
#endif

#ifndef __GNUC__
#define NULL 0
#endif

int g;

void *t1(void *arg)
{
  int a1, *aptr1;
  
  aptr1=(int *)arg;
  a1=*aptr1;
  g=0;
  // this should pass
  assert(a1==10);
  assert(g==0);

  return NULL;
}

void *t2(void *arg)
{
  int a2, *aptr2;
  
  aptr2=(int *)arg;
  a2=*aptr2;
  g=0;
  // this should pass
  assert(a2==20);

  return NULL;
}

int main()
{
#ifdef __GNUC__
  pthread_t id1, id2;
#endif  
  int arg1=10, arg2=20;
#ifdef __GNUC__
  pthread_create(&id1, NULL, t1, &arg1);
  pthread_create(&id2, NULL, t2, &arg2);
#endif
  assert(g==0);
#ifdef __GNUC__
  pthread_join(id1, NULL);
  pthread_join(id2, NULL);
#endif
  return 0;
}
