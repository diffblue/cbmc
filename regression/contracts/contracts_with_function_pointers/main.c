#include <assert.h>
#include <stddef.h>

int x;

void foo(int *y)
{
  *y = 1;
}

int *baz()
{
  return &x;
}

void bar(void (*fun_ptr)(), int *x) __CPROVER_requires(fun_ptr != NULL)
  __CPROVER_requires(x != NULL) __CPROVER_assigns(*x) __CPROVER_ensures(*x == 1)
{
  *(baz()) = 1;
  fun_ptr(x);
}

int main()
{
  x = 0;
  void (*fun_ptr)() = foo;
  bar(fun_ptr, &x);
  assert(x == 1);
  return 0;
}
