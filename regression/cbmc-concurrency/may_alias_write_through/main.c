// Test write through a shared pointer in concurrent context.
#include <assert.h>

int *shared_ptr;
int val;
_Bool done;

void writer(void)
{
  shared_ptr = &val;
  done = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: writer();
  __CPROVER_assume(done == 1);
  *shared_ptr = 42;
  assert(val == 42);
}
