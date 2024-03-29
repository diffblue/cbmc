#include <assert.h>

typedef int (*fptr_t)(long long);

void use_f(fptr_t fptr)
{
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  assert(fptr(10) == 11);
#else
  if(sizeof(int) == sizeof(long long))
    assert(fptr(10) == 11);
  else
    assert(fptr(10) == 1);
#endif
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
