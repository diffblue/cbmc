// Benchmark built by Alex Horn
// This simple C file illustrates how to join multiple threads
// in the context of bounded model checking and partial order
// program semantics as implemented in CBMC 4.5 and higher.
#include <assert.h>

// ========= Thread Group library =========

// Internal shared global variable, zero initially
unsigned thread_counter;

// Public function pointer to an thread handler routine
typedef void (*thread_handler_t)();

// `start_thread` and `join_all_threads`
// must be only executed from the same thread
void start_thread(thread_handler_t thread_handler)
{
  __CPROVER_atomic_begin();
  ++thread_counter;
  __CPROVER_atomic_end();

  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");

  __CPROVER_ASYNC_1: thread_handler(),
                     __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                                     "WWcumul", "RRcumul", "RWcumul", "WRcumul"),
                     --thread_counter;
}

void join_all_threads()
{
  __CPROVER_assume(thread_counter == 0);
}

// ========= Symbolic test =========

// Global variable to test threads
char c;

void thread_0()
{
  c = 'A';
}

void thread_1()
{
  c = 'B';
}

void test_1(void)
{
  start_thread(thread_0);

#ifdef _EXPECT_PASS_
  join_all_threads();
#endif

  // fails unless _EXPECT_PASS_
  assert(c == 'A');

  start_thread(thread_1);

#ifdef _EXPECT_PASS_
  join_all_threads();
#endif

  // fails unless _EXPECT_PASS_
  assert(c == 'B');

  return 1;
}

void test_2(void)
{
  start_thread(thread_0);
  start_thread(thread_1);

#ifdef _EXPECT_PASS_
  join_all_threads();
#endif

  // fails unless _EXPECT_PASS_
  assert(c == 'A' || c == 'B');

  return 1;
}

int main(void)
{
#ifdef _TEST_1_
  test_1();
#endif

#ifdef _TEST_2_
  test_2();
#endif

  return 1;
}
