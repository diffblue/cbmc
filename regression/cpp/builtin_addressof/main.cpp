#include <assert.h>

int main()
{
  int x = 42;
  int *p = __builtin_addressof(x);
  assert(*p == 42);
}
