// Test that may-alias handles type-compatible (same-size) types.
// shared_ptr is int* but points to an unsigned int.
#include <assert.h>

int *shared_ptr;
unsigned int val_unsigned;
_Bool done;

void writer(void)
{
  val_unsigned = 42;
  shared_ptr = (int *)&val_unsigned;
  done = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: writer();
  __CPROVER_assume(done == 1);
  assert(*shared_ptr == 42);
}
