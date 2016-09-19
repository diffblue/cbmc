#include <pthread.h>
#include <assert.h>

int s[2];

void* thread_0(void* arg)
{
  s[0] = 2;
  assert(s[0] == 2);
  return NULL;
}

void* thread_1(void* arg)
{
  s[1] = 1;
  assert(s[1] == 1);
  return NULL;
}

int main(void)
{
  pthread_t thread0, thread1;
  pthread_create(&thread0, NULL, thread_0, 0);
  pthread_create(&thread1, NULL, thread_1, 0);
  return 0;
}
