#include <assert.h>

int main()
{
  int x;
  int *p = &x;
  *p = 42;
  assert(x == 42);
  return 0;
}
