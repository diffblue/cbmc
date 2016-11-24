// Benchmark built by Alex Horn
// expect assertion violation if and only if
// - cbmc -D_SANITY_CHECK_ thread_chain_cbmc.c
#include <assert.h>

#ifndef NULL
#define NULL 0
#endif

// ========= Thread Chain library =========

// Internal thread local identifier of a thread

// The benefit of local thread identifiers is that CBMC is more likely
// to be able to perform constant propagation on thread identifiers.
// The downside is that the public interface requires the user to
// choose thread identifiers such that they are globally unique.
typedef unsigned long thread_id_t;

// Internal unbounded array indexed by local thread identifiers
extern __CPROVER_bool __CPROVER_threads_exited[];

// A thread_chain is like a chain of threads `f, g, ...` where `f`
// must terminate before `g` can start to run, and so forth.
typedef thread_id_t thread_chain_t;

// Initialize thread_chain
//
// Note that `init_thread_id` will be incremented on each `thread_chain_run`
// call in order to to generate a new thread identifier. It is the
// responsibility of the caller to ensure that the resulting thread
// identifiers are globally unique.
//
// So pick `init_thread_id` according to how many threads will be
// spawned across different threads in the system.
thread_chain_t make_thread_chain(thread_id_t init_thread_id)
{
  // the first thread in the chain of threads is ready to to run
  __CPROVER_threads_exited[init_thread_id] = 1;

  return (thread_chain_t) init_thread_id;
}

// Public function pointer
typedef void (*start_routine)(void *);

// Internal start routine for a new thread in a thread_chain that waits on `thread_id`
//
// \pre: `f` is not null
static void thread_chain_start_routine(thread_id_t thread_id, start_routine f, void *arg)
{
  __CPROVER_assume(__CPROVER_threads_exited[thread_id]);

  f(arg);
}

// Create a new thread for `f` where `f(arg)` starts to run as
// soon as the currently running thread in `thread_chain` has terminated.
int thread_chain_run(thread_chain_t *thread_chain, start_routine f, void *arg)
{
  assert(f != NULL);

  thread_id_t current_thread_id, thread_id;

  __CPROVER_atomic_begin();
  current_thread_id = (thread_id_t) *thread_chain;
  thread_id = current_thread_id + 1;
  *thread_chain = (thread_chain_t) thread_id;
  __CPROVER_atomic_end();

  __CPROVER_ASYNC_1: thread_chain_start_routine(current_thread_id, f, arg),
                     __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                                     "WWcumul", "RRcumul", "RWcumul", "WRcumul"),
                     __CPROVER_threads_exited[thread_id] = 1;
}

// ========= Symbolic test =========

char test_global;

void test_write_a(void *arg)
{
  test_global = 'A';
}

void test_write_b(void *arg)
{
  test_global = 'B';
}

int main(void)
{
  thread_chain_t thread_chain = make_thread_chain(0UL);

  thread_chain_run(&thread_chain, test_write_a, NULL);
  thread_chain_run(&thread_chain, test_write_b, NULL);

  char x = test_global;
  char y = test_global;

  // Verification condition:
  //
  //  If global variable equals 'B', then it cannot change.
  assert(x != 'B' || y == 'B');

#ifdef _SANITY_CHECK_
  // can be violated regardless of _ENABLE_CHAIN_
  assert(x != 'A' || y == 'A');
#endif

  return 0;
}
