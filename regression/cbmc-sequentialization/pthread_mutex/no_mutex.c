#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

int shared_count = 0;

void *worker(void *arguments)
{
  for(int i = 0; i < 100; ++i)
  {
    int shared_count_copy = shared_count;
    // The following call to yield is here in order to increase the chance of
    // thread swaps during concrete execution in order to show unsoundness.
    sched_yield();
    ++shared_count_copy;
    shared_count = shared_count_copy;
  }
  pthread_exit(NULL);
}

pthread_t start_worker_thread(void)
{
  pthread_t worker_thread;
  const pthread_attr_t *const attributes = NULL;
  void *const worker_argument = NULL;
  const int create_status =
    pthread_create(&worker_thread, attributes, &worker, worker_argument);
  assert(create_status == 0);
  return worker_thread;
}

void join_thread(const pthread_t thread)
{
  const int join_status = pthread_join(thread, NULL);
  assert(join_status == 0);
}

int main(void)
{
  const pthread_t worker_thread1 = start_worker_thread();
  const pthread_t worker_thread2 = start_worker_thread();
  join_thread(worker_thread1);
  join_thread(worker_thread2);

  // Check if the shared count has been incremented 200 times.
  printf("The shared count is %d.\n", shared_count);
  assert(shared_count == 200);
  return EXIT_SUCCESS;
}
