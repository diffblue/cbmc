#include <assert.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdbool.h>
#include <stdlib.h>

pthread_t start_worker_thread(void *(*start_routine)(void *))
{
  pthread_t worker_thread;
  const pthread_attr_t *const attributes = NULL;
  void *const worker_argument = NULL;
  const int create_status =
    pthread_create(&worker_thread, attributes, start_routine, worker_argument);
  assert(create_status == 0);
  return worker_thread;
}

void join_thread(const pthread_t thread)
{
  const int join_status = pthread_join(thread, NULL);
  assert(join_status == 0);
}

sem_t create_semaphore(int initial_value)
{
  const int shared_between_processes = false;
  sem_t semaphore;
  const int init_error =
    sem_init(&semaphore, shared_between_processes, initial_value);
  assert(init_error == false);
  return semaphore;
}

void destroy_semaphore(sem_t *const semaphore)
{
  int destroy_error = sem_destroy(semaphore);
  assert(destroy_error == false);
}

sem_t global_semaphore;
int global_value;

void *worker(void *arguments)
{
  const int wait_error = sem_wait(&global_semaphore);
  assert(wait_error == false);
  assert(global_value == 42);
  pthread_exit(NULL);
}

int main(void)
{
  global_semaphore = create_semaphore(0);
  global_value = 0;

  const pthread_t worker_thread1 = start_worker_thread(&worker);
  global_value = 42;
  const int post_error = sem_post(&global_semaphore);
  assert(post_error == false);
  join_thread(worker_thread1);

  destroy_semaphore(&global_semaphore);
  return EXIT_SUCCESS;
}
