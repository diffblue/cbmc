#include <assert.h>

int *ptr;
int val;
_Bool done;

void writer(void)
{
  val = 42;
  ptr = &val;
  done = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: writer();
  __CPROVER_assume(done == 1);
  assert(*ptr == 42);
}
