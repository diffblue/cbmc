#include <pthread.h>
 
int x;
 
void *thr2(void *arg)
{
  ++x;
}
 
 
int main()
{
  pthread_t tid2;
  pthread_create(&tid2, NULL, thr2, NULL);
 
  pthread_join(tid2, NULL);
 
  return 0;
}
