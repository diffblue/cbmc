#include <pthread.h>
#include <stdlib.h>
#include <assert.h>

int x = 0, y;

void* thr1(void * arg)
{
  y = 1;
  // will fail under tso/pso unless pthread_create implies
  // a barrier
  assert(x != 0);
}

int main()
{
  x = 1;
  pthread_create(NULL, NULL, thr1, NULL);
}
