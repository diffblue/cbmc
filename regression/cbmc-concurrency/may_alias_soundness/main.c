// Soundness test: the assertion MUST fail.
// writer() sets ptr to &val2 (which is 99), so *ptr != 42 is possible.
#include <assert.h>

int *ptr;
int val1, val2;
_Bool done;

void writer(void)
{
  val1 = 42;
  val2 = 99;
  ptr = &val2;
  done = 1;
}

int main(void)
{
  ptr = &val1;
  __CPROVER_ASYNC_1: writer();
  __CPROVER_assume(done == 1);
  assert(*ptr == 42);
}
