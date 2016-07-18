#include <pthread.h>
 
void * thr (void * arg)
{
  return 0;
}

int vi;

void foo ()
{
	vi = 1;

	pthread_t tid;

	pthread_create(&tid, 0, thr, 0);
}

int main (void)
{
	vi = 0;

	foo ();

  return 0;
}
