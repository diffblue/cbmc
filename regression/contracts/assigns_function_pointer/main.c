#include <assert.h>
#include <stddef.h>

int x = 0;

void foo()
{
  x = 1;
}

void bar(void (*fun_ptr)()) __CPROVER_assigns(fun_ptr)
{
  fun_ptr = &foo;
}

int main()
{
  assert(x == 0);
  void (*fun_ptr)() = NULL;
  bar(fun_ptr);
  fun_ptr();
  assert(x == 1);
  return 0;
}
