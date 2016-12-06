#include <pthread.h>
#include <assert.h>

int i=0;

void* foo(void *arg)
{
  __CPROVER_atomic_begin();
  ++i;
  __CPROVER_atomic_end();
  return 0;
}

int main()
{
  pthread_t th1, th2;
  pthread_create(&th1, 0, foo, 0);
  pthread_create(&th2, 0, foo, 0);
  pthread_join(th1, 0);
  pthread_join(th2, 0);
  assert(i==1); // should fail, as there are two threads
  assert(i==2); // should pass
}
