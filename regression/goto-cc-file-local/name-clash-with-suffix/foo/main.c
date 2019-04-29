#include <assert.h>

int bar();

static int static_fun()
{
  return bar();
}

int main()
{
  assert(static_fun() == 3);
}
