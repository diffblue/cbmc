#include <assert.h>

int foo(int i)
{
  return i + 1;
}

int (*fun_ptr)(int);

void initialize()
{
  fun_ptr = &foo;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(fun_ptr == &foo);
  assert((*fun_ptr)(5) == 6);
  assert((*fun_ptr)(5) == foo(5));
  return 0;
}
