/* This test checks if the tool
   can find out that function thr1
   is executed by multiple threads,
   due to the thread-creation loop. */


#include <pthread.h>

int x;

void thr1()
{
  x=0;
}


void spawn()
{
  pthread_t tid;
  pthread_create(&tid, NULL, thr1, NULL);
}


void spawn_loop(unsigned n)
{
  unsigned i=0;

  for(i=0; i<n; ++i)
  {
    spawn();
  }
}

int main()
{
  spawn_loop(10);
}
