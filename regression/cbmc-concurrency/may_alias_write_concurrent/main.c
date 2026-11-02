// Two threads write through shared pointer with synchronization.
// thread2 writes 42 after thread1, main reads after thread2.
// Must verify successfully — no false positives.
#include <assert.h>

int *shared_ptr;
int val;
_Bool step1_done, step2_done;

void thread1(void)
{
  shared_ptr = &val;
  *shared_ptr = 10;
  step1_done = 1;
}

void thread2(void)
{
  __CPROVER_assume(step1_done == 1);
  *shared_ptr = 42;
  step2_done = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: thread1();
  __CPROVER_ASYNC_2: thread2();
  __CPROVER_assume(step2_done == 1);
  assert(*shared_ptr == 42);
}
