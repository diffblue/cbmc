#include <pthread.h>
#include <assert.h>

int f0, f1;

void* thread_0(void* arg)
{
  f0 = 2;
  assert(f0 == 2);
  return NULL;
}

void* thread_1(void* arg)
{
  f1 = 1;
  assert(f1 == 1);
  return NULL;
}

int main(void)
{
  pthread_t thread0, thread1;
  pthread_create(&thread0, NULL, thread_0, 0);
  pthread_create(&thread1, NULL, thread_1, 0);
  return 0;
}
