#include <assert.h>

typedef int (*fptr_t)(int);

void use_f(fptr_t fptr)
{
labelled_call:
  assert(fptr(10) == 11);
}

int f(int x)
{
  return x + 1;
}

int g(int x)
{
  return x;
}

int main(void)
{
  int one = 1;

  // We take the address of f and g. In this case remove_function_pointers()
  // would create a case distinction involving both f and g in the function
  // use_f() above.
  use_f(one ? f : g);
}
