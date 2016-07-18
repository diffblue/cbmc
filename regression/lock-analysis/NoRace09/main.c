#include <pthread.h>
 
pthread_mutex_t mtx_;
pthread_mutex_t * const mtx = &mtx_;

void * thr (void * arg)
{
	pthread_mutex_lock (mtx);
	pthread_mutex_unlock (mtx);
	return 0;
}

int main ()
{
	pthread_t tid;

	pthread_mutex_init (mtx, 0);

	pthread_create (&tid, 0, thr, 0);

	pthread_join (tid, 0);

	pthread_mutex_destroy (mtx);

  return 0;
}
