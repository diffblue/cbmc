// Test that local pointers derived from shared sources are handled
// correctly by the may-alias mechanism.
#include <assert.h>

int *shared_ptr;
int val1, val2;
_Bool done;

void writer(void)
{
  val1 = 42;
  val2 = 99;
  shared_ptr = &val2;
  done = 1;
}

int main(void)
{
  shared_ptr = &val1;
  __CPROVER_ASYNC_1: writer();
  __CPROVER_assume(done == 1);

  // Direct dereference of shared pointer
  assert(*shared_ptr == 42);

  // Copy to local, then dereference — must also detect the bug
  int *local_ptr = shared_ptr;
  assert(*local_ptr == 42);
}
