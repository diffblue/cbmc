// Run as: cbmc --unwind 1 bug2.c

#include <pthread.h>
#include <assert.h>

int flag;

void *p1(void *arg)
{
  int i;
  while (__sync_bool_compare_and_swap(&flag, 0, 1)) {}
  return 0;
}

int main()
{
  pthread_t t1, t2;
  flag = 0;
  pthread_create(&t1, 0, p1, 0);
  pthread_join(t1, 0);
  return 0;
}
