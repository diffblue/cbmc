// uninitialized locks should still be tracked

#include <pthread.h>

pthread_mutex_t lock1;
pthread_mutex_t lock2;
pthread_mutex_t lock3;

int main()
{
  pthread_mutex_lock(&lock1); 
  pthread_mutex_lock(&lock2);
  pthread_mutex_lock(&lock3);

  return 0;
}

