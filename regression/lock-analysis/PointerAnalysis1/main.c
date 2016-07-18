// deadlock

#include <pthread.h>

struct th_arg
{
  pthread_mutex_t m1,m2;
};

int x;

void *thr1(void *arg)
{
  struct th_arg *t = (struct th_arg *)arg;
  pthread_mutex_lock(&t->m1);
  pthread_mutex_lock(&t->m2);
  ++x;
  pthread_mutex_unlock(&t->m2);
  pthread_mutex_unlock(&t->m1);
}

void *thr2(void *arg)
{
  struct th_arg *t = (struct th_arg *)arg;
  pthread_mutex_lock(&t->m1);
  pthread_mutex_lock(&t->m2);
  ++x;
  pthread_mutex_unlock(&t->m2);
  pthread_mutex_unlock(&t->m1);
}

int main()
{
  pthread_t tid1, tid2;
  struct th_arg t;
  pthread_create(&tid1, NULL, thr1, (void *)&t);
  pthread_create(&tid2, NULL, thr2, (void *)&t);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);

  return 0;
}
