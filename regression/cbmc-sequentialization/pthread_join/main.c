#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

void *worker(void *arguments)
{
  int *return_value = malloc(sizeof(int));
  *return_value = 42;
  pthread_exit(return_value);
}

int main(void)
{
  pthread_t thread;
  const pthread_attr_t *const attributes = NULL;
  void *const worker_argument = NULL;
  int create_status =
    pthread_create(&thread, attributes, &worker, worker_argument);
  assert(create_status == 0);
  int *worker_return;
  int join_status = pthread_join(thread, (void **)&worker_return);
  assert(join_status == 0);
  printf("Thread return value is %d.\n", *worker_return);
  assert(*worker_return == 42);
  free(worker_return);
  return EXIT_SUCCESS;
}
