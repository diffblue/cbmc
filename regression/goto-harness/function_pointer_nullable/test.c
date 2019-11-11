#include <assert.h>
#include <stdlib.h>

typedef int (*fptr_t)(void);

void entry_point(fptr_t f, fptr_t f_but_may_be_null)
{
  assert(f != (void *)0);                 // expected to succeed
  assert(f == (void *)0);                 // expected to fail
  assert(f_but_may_be_null != (void *)0); // expected to fail
  assert(f_but_may_be_null == (void *)0); // expected to fail
  assert(f_but_may_be_null == (void *)0 || f() == f_but_may_be_null());
}

int f(void)
{
  return 42;
}
