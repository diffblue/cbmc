#include <assert.h>

int x;

__attribute__((destructor(100))) static void reserved_destructor(void)
{
}

__attribute__((constructor(0))) static void reserved_constructor(void)
{
  x = 1;
}

int main()
{
  assert(x == 1);
  return 0;
}
