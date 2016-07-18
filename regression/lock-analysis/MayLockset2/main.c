#include <pthread.h>

pthread_mutex_t lock1=PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock2=PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock3=PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock4=PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock5=PTHREAD_MUTEX_INITIALIZER;

void func2(int i)
{
  if(i)
  {
    while(1)
    {
      pthread_mutex_lock(&lock5);
    }
  }
}

void func()
{
  pthread_mutex_lock(&lock4);
  func2(10);
}

int main()
{
  int x;

  pthread_mutex_lock(&lock1); 
  if (x)
    pthread_mutex_lock(&lock2);
  else
    pthread_mutex_lock(&lock3);

  if (!x)
    func();

  x = 1;

  return 0;
}

