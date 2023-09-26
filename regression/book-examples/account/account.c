#include <assert.h>
#include <pthread.h>

pthread_mutex_t mutex;
int balance = 1000;

void *transaction(void *amount)
{
  // pthread_mutex_lock(&mutex);
  int current = balance;
  current += *(int *)amount;
  balance = current;
  // pthread_mutex_unlock(&mutex);
  return 0;
}

int main()
{
  pthread_t t1, t2;
  pthread_mutex_init(&mutex, 0);

  int amount1 = -3000;
  pthread_create(&t1, 0, transaction, &amount1);
  int amount2 = 8000;
  pthread_create(&t2, 0, transaction, &amount2);

  pthread_join(t1, 0);
  pthread_join(t2, 0);
  assert(balance == 6000);

  pthread_mutex_destroy(&mutex);
  return 0;
}
