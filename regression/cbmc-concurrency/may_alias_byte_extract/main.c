// Test char* accessing an int through shared pointer (byte_extract).
#include <assert.h>

char *shared_ptr;
int val;
_Bool done;

void writer(void)
{
  val = 0x42;
  shared_ptr = (char *)&val;
  done = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: writer();
  __CPROVER_assume(done == 1);
  assert(*shared_ptr == 0x42);
}
