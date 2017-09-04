#include <assert.h>

int foo()
{
  assert(0);
  return 0;
}

int main(void)
{
  int (*p)()=&foo;
  return p();
}
