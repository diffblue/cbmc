#include <pthread.h>
#include <assert.h>

int *v;
int g;

void *thread1(void * arg)
{
  v = &g;
}

void *thread2(void *arg)
{
  assert(v == &g);
  *v = 1;
}

int main()
{
  pthread_t t1, t2;

  pthread_create(&t1, 0, thread1, 0);
  pthread_join(t1, 0);

  pthread_create(&t2, 0, thread2, 0);
  pthread_join(t2, 0);

  assert(v == &g);
  assert(*v == 1);

  return 0;
}
