#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

pthread_t worker_self_thread;

void *worker(void *arguments)
{
  // Check pthread_self() returns a consistent value.
  const pthread_t self1 = pthread_self();
  const pthread_t self2 = pthread_self();
  assert(pthread_equal(self1, self2));

  worker_self_thread = self1;
  pthread_exit(NULL);
}

int main(void)
{
  pthread_t worker_thread;
  const pthread_attr_t *const attributes = NULL;
  void *const worker_argument = NULL;
  const int create_status =
    pthread_create(&worker_thread, attributes, &worker, worker_argument);
  assert(create_status == 0);
  const int join_status = pthread_join(worker_thread, NULL);
  assert(join_status == 0);

  // Check main thread self is different from worker thread self.
  const pthread_t main_thread = pthread_self();
  assert(!pthread_equal(main_thread, worker_self_thread));
  return EXIT_SUCCESS;
}
