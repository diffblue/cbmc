#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

int shared_global;
pthread_mutex_t signal_mutex;
pthread_cond_t condition;
bool signal_sent;

void initialise_condition(void)
{
  pthread_mutexattr_t *mutex_attributes = NULL;
  int pthread_mutex_init_error =
    pthread_mutex_init(&signal_mutex, mutex_attributes);
  assert(!pthread_mutex_init_error);

  pthread_condattr_t *condition_attributes = NULL;
  int condition_init_error =
    pthread_cond_init(&condition, condition_attributes);
  assert(!condition_init_error);
}

// Wait for signal. Note that pthreads requires us to lock and unlock the mutex
// around the call to `pthread_cond_wait`. Note also that if called
// pthread_cond_wait function waits then it will leave the mutex unlocked whilst
// it is waiting.
void wait(void)
{
  const int lock_error = pthread_mutex_lock(&signal_mutex);
  assert(!lock_error);
  const int wait_error = pthread_cond_wait(&condition, &signal_mutex);
  assert(!wait_error);
  const int unlock_error = pthread_mutex_unlock(&signal_mutex);
  assert(!unlock_error);
}

void signal(void)
{
  const int lock_error = pthread_mutex_lock(&signal_mutex);
  assert(!lock_error);
  int signal_error = pthread_cond_signal(&condition);
  assert(!signal_error);
  const int unlock_error = pthread_mutex_unlock(&signal_mutex);
  assert(!unlock_error);
}

void *worker(void *arguments)
{
  shared_global = 42;
  signal_sent = true;
  signal();
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
  shared_global = 0;
  signal_sent = false;
  const pthread_t worker_thread1 = start_worker_thread();
  while(!signal_sent)
  {
    wait();
  }
  assert(shared_global == 42);
  join_thread(worker_thread1);

  pthread_mutex_destroy(&signal_mutex);
  pthread_cond_destroy(&condition);
  return EXIT_SUCCESS;
}
