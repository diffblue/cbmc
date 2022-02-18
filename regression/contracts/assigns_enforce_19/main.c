#include <assert.h>

static int b = 0;
static int c = 0;

int f() __CPROVER_assigns()
{
  static int a = 0;
  static int aa = 0;
  a++;
  aa++;
  return a;
}

int g(int *points_to_b, int *points_to_c)
  __CPROVER_assigns(b) // Error: it should also mention c
{
  b = 1;
  c = 2;
  *points_to_b = 1;
  *points_to_c = 2;
}

int main()
{
  assert(f() == 1);
  assert(f() == 2);
  assert(b == 0);
  assert(c == 0);
  g(&b, &c);
  assert(b == 1);
  assert(c == 2);

  return 0;
}
