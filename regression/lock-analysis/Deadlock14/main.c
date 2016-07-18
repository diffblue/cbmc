// deadlock

#include <pthread.h>

pthread_mutex_t m1,m2;

int x;

void *thr(void *arg)
{
  pthread_mutex_lock(&m1);
  pthread_mutex_lock(&m2);
  ++x;
  pthread_mutex_unlock(&m2);
  pthread_mutex_unlock(&m1);

  int k=0;

  pthread_mutex_lock(&m2);
  pthread_mutex_lock(&m1);
  ++x;
  pthread_mutex_unlock(&m1);
  pthread_mutex_unlock(&m2);

  k++;
}

void spawn(pthread_t tid[], int i)
{
  pthread_create(&tid[i], NULL, thr, NULL);
}

int main()
{
  int no_threads = 2;
  pthread_t tid[no_threads];
  for(int i=0; i<no_threads; i++)
    spawn(tid,i);

  for(int i=0; i<no_threads; i++)
    pthread_join(&tid[i], NULL);

  return 0;
}
