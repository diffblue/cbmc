#include <assert.h>

int foo()
{
  return 10;
}

int bar()
{
  return 5;
}

int main()
{
  int (*fun_ptr)() = nondet_bool() ? &foo : &bar;
  assert(fun_ptr() == 10);
}
