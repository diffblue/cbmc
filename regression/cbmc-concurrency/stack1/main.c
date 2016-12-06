#include <pthread.h>
#include <assert.h>

void *thread(void *arg)
{
  int *i = (int *)arg;
  *i = 1;
}

int main(void)
{
  int x;
  x = 0;

  pthread_t t;

  pthread_create(&t, NULL, thread, &x);
  pthread_join(t, NULL);

  assert(x == 1);

  return 0;
}
