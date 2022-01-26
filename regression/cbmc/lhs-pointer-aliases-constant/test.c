#include <assert.h>

int main()
{
  int x;
  const char *c = "Hello world";
  _Bool dummy;
  __CPROVER_assume(dummy);

  int *p = (dummy ? &x : (int *)c);

  *p = 1;

  assert(*p == 1);

  return 0;
}
