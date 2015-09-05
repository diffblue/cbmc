// Benchmark built by Alex Horn
// cbmc thread_chain_posix.c: assertion violation since we only use regular threads
// cbmc -D_ENABLE_CHAIN_ --unwind 2 thread_chain_posix.c: no assertion violation
// cbmc -D_ENABLE_CHAIN_ -D_SANITY_CHECK_ --unwind 2 thread_chain_posix.c: assertion violation
#include <pthread.h>
#include <assert.h>

#ifndef _ENABLE_MEMORY_BUG_
#include <stdlib.h>

void *malloc(size_t size);
void free(void* ptr);
#endif

// Define _EXPOSE_BUG_ when _ENABLE_CHAIN_ is undefined in
// order to get an executable that shows the effect of
// using thread_chains instead of regular threads.
#if defined(_EXPOSE_BUG_) || defined(_EXPOSE_SANITY_CHECK_)
#include <unistd.h>

#define TINY_DELAY 1
#define SHORT_DELAY 3
#define LONG_DELAY 5
#endif

// ========= Chain library =========

// This struct is not thread-safe itself!
//
// A thread_chain is like a chain of threads `f, g, ...` where `f`
// must terminate before `g` can start to run, and so forth.
struct thread_chain_t
{
  // last thread in chain
  pthread_t thread;
};

// Public function pointer
typedef void *(*start_routine)(void *);

// Internal
struct thread_chain_args_t
{
  // last thread in chain
  pthread_t thread;

  // function pointer for new thread, never null
  start_routine f;

  // argument to f, possibly null
  void *f_arg;
};

// Internal start routine for a thread in a thread_chain
static void* thread_chain_start_routine(void *ptr)
{
  struct thread_chain_args_t *args = (struct thread_chain_args_t *) ptr; 

  // ignore errors
  pthread_join(args->thread, NULL);

  assert(args->f != NULL);
  void* r = args->f(args->f_arg);

#ifndef _ENABLE_MEMORY_BUG_
  free(args);
#endif

  pthread_exit(NULL);
  return r;
}

// This function is not thread-safe itself!
//
// Create a new thread for `f` where `f(arg)` starts to run as
// soon as the currently running `self->thread` has terminated.
//
// \post: `self->thread` is the newly created thread for `f`
int thread_chain_run(struct thread_chain_t *self, start_routine f, void *arg)
{
#ifdef _ENABLE_MEMORY_BUG_
  struct thread_chain_args_t local_args;
  struct thread_chain_args_t *args = &local_args;
#else
  // since the address of a local variable results
  // in undefined behaviour when thread_chain_run returns,
  // we allocate a thread_chain_args_t struct instead in
  // case thread_chain_start_routine outlives thread_chain_run.
  struct thread_chain_args_t *args = malloc(sizeof(struct thread_chain_args_t));
  if (!args)
    return -1;
#endif

  args->thread = self->thread;
  args->f = f;
  args->f_arg = arg;

  return pthread_create(&(self->thread), NULL, thread_chain_start_routine, (void *) args);
}

// ========= Symbolic test =========

char test_global;

void* test_write_a(void *arg)
{
#ifdef _EXPOSE_BUG_
  sleep(SHORT_DELAY);
#endif

  test_global = 'A';
  return NULL;
}

void* test_write_b(void *arg)
{
#ifdef _EXPOSE_SANITY_CHECK_
  sleep(SHORT_DELAY);
#endif

  test_global = 'B';
  return NULL;
}

int main(void)
{
#ifdef _ENABLE_CHAIN_
  struct thread_chain_t thread_chain;
  thread_chain_run(&thread_chain, test_write_a, NULL);
  thread_chain_run(&thread_chain, test_write_b, NULL);
#else
  pthread_t a_thread, b_thread;
  pthread_create(&a_thread, NULL, test_write_a, NULL);
  pthread_create(&b_thread, NULL, test_write_b, NULL);
#endif

#if defined(_EXPOSE_BUG_) || defined(_EXPOSE_SANITY_CHECK_)
  sleep(TINY_DELAY);
#endif

  char x = test_global;

#if defined(_EXPOSE_BUG_) || defined(_EXPOSE_SANITY_CHECK_)
  sleep(LONG_DELAY);
#endif

  char y = test_global;

  // Verification condition:
  //
  //  If global variable equals 'B', then it cannot change.
  //
  // It is expected that this implication
  // fails if _ENABLE_CHAIN_ is undefined.
  assert(x != 'B' || y == 'B');

#ifdef _SANITY_CHECK_
  // can be violated regardless of _ENABLE_CHAIN_
  assert(x != 'A' || y == 'A');
#endif

#ifdef _ENABLE_CHAIN_
  // the other joins happen in the chain of threads
  pthread_join(thread_chain.thread, NULL);
#else
  pthread_join(a_thread, NULL);
  pthread_join(b_thread, NULL);
#endif

  return 0;
}
