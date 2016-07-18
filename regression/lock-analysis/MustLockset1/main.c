#include <pthread.h>

pthread_mutex_t lock1=PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock2=PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock3=PTHREAD_MUTEX_INITIALIZER;

int main()
{
  int x;

  pthread_mutex_lock(&lock1); 
  if (x)
  {
    pthread_mutex_lock(&lock2);
    x = 1;
  }
  else
  {
    pthread_mutex_lock(&lock3);
    x = 2;
  }

  x = 3;

  return 0;
}

