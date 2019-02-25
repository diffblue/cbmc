#include <assert.h>
#include <pthread.h>

pthread_mutex_t lock;
pthread_cond_t cond;

// only accessed in critical section guarded by mutex, so there is no need to
// make this variable atomic or volatile
int x;

void *thread(void *arg)
{
  (void)arg;
  pthread_mutex_lock(&lock);
  pthread_cond_wait(&cond, &lock);
  // may fail: pthread_cond_wait can be waken up spuriously (see man
  // pthread_cond_wait)
  assert(x == 1);
  pthread_mutex_unlock(&lock);
  return NULL;
}

int main()
{
  pthread_t t;
  pthread_mutex_init(&lock, 0);
  pthread_cond_init(&cond, 0);
  pthread_create(&t, NULL, thread, NULL);
  x = 1;
  pthread_cond_broadcast(&cond);
  pthread_join(t, NULL);
}
