// Test --refine-concurrency produces correct results.
#include <assert.h>

int *shared_ptr;
int val;
_Bool done;

void writer(void)
{
  val = 42;
  shared_ptr = &val;
  done = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: writer();
  __CPROVER_assume(done == 1);
  assert(*shared_ptr == 42);
}
