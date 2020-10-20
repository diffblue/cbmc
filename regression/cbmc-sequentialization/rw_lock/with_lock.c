#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

struct sharedt
{
  pthread_rwlock_t lock;
  int a;
  int b;
  int c;
};

void set_state1(struct sharedt *shared)
{
  shared->a = 1;
  shared->b = 2;
  // The following call to yield is here in order to increase the chance of
  // thread swaps during concrete execution in order to show unsoundness.
  sched_yield();
  shared->c = 3;
}

void set_state2(struct sharedt *shared)
{
  shared->a = 4;
  shared->b = 5;
  // The following call to yield is here in order to increase the chance of
  // thread swaps during concrete execution in order to show unsoundness.
  sched_yield();
  shared->c = 6;
}

void *writer1(void *arguments)
{
  struct sharedt *shared = (struct sharedt *)arguments;
  for(int i = 0; i < 1000; ++i)
  {
    const int lock_error = pthread_rwlock_wrlock(&(shared->lock));
    assert(!lock_error);
    set_state1(shared);
    const int unlock_error = pthread_rwlock_unlock(&(shared->lock));
    assert(!unlock_error);
  }
  pthread_exit(NULL);
}

void *writer2(void *arguments)
{
  struct sharedt *shared = (struct sharedt *)arguments;
  for(int i = 0; i < 1000; ++i)
  {
    const int lock_error = pthread_rwlock_wrlock(&(shared->lock));
    assert(!lock_error);
    set_state2(shared);
    const int unlock_error = pthread_rwlock_unlock(&(shared->lock));
    assert(!unlock_error);
  }
  pthread_exit(NULL);
}

void *checker(void *arguments)
{
  struct sharedt *shared = (struct sharedt *)arguments;
  for(int i = 0; i < 1000; ++i)
  {
    const int lock_error = pthread_rwlock_rdlock(&(shared->lock));
    assert(!lock_error);
    const bool is_state1 = shared->a == 1 && shared->b == 2 && shared->c == 3;
    // The following call to yield is here in order to increase the chance of
    // thread swaps during concrete execution in order to show unsoundness.
    sched_yield();
    const bool is_state2 = shared->a == 4 && shared->b == 5 && shared->c == 6;
    assert(is_state1 != is_state2);
    const int unlock_error = pthread_rwlock_unlock(&(shared->lock));
    assert(!unlock_error);
    printf(is_state1 ? "State1\n" : "State2\n");
  }
  pthread_exit(NULL);
}

int main(void)
{
  struct sharedt shared;
  set_state1(&shared);
  const pthread_rwlockattr_t *init_attributes = NULL;
  const int init_error = pthread_rwlock_init(&(shared.lock), init_attributes);
  assert(!init_error);

  const pthread_attr_t *const attributes = NULL;
  void *const thread_argument = &shared;
  pthread_t thread_writer1;
  assert(
    !pthread_create(&thread_writer1, attributes, &writer1, thread_argument));
  pthread_t thread_writer2;
  assert(
    !pthread_create(&thread_writer2, attributes, &writer2, thread_argument));

  pthread_t thread_checker1;
  pthread_t thread_checker2;
  pthread_t thread_checker3;
  assert(
    !pthread_create(&thread_checker1, attributes, &checker, thread_argument));
  assert(
    !pthread_create(&thread_checker2, attributes, &checker, thread_argument));
  assert(
    !pthread_create(&thread_checker3, attributes, &checker, thread_argument));

  assert(!pthread_join(thread_writer1, NULL));
  assert(!pthread_join(thread_writer2, NULL));
  assert(!pthread_join(thread_checker1, NULL));
  assert(!pthread_join(thread_checker2, NULL));
  assert(!pthread_join(thread_checker3, NULL));

  const int destroy_error = pthread_rwlock_destroy(&(shared.lock));
  assert(!destroy_error);
  return EXIT_SUCCESS;
}
