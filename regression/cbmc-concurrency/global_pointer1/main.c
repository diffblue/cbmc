#include <pthread.h>
#include <assert.h>

int *v;
int g;

void *thread1(void * arg)
{
  v = &g;
  return NULL;
}

void *thread2(void *arg)
{
  assert(v == &g);
#ifndef NO_DEREF
  *v = 1;
#endif
  return NULL;
}

int main()
{
  pthread_t t1, t2;

  pthread_create(&t1, 0, thread1, 0);
  pthread_join(t1, 0);

  pthread_create(&t2, 0, thread2, 0);
  pthread_join(t2, 0);

  assert(v == &g);
#ifndef NO_DEREF
  assert(*v == 1);
#endif

  return 0;
}
