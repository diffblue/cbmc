#include <assert.h>

struct S
{
  int x;
};

struct T
{
  struct S a[2];
};

int main()
{
  struct T t;
  t.a[1].x = 42;
  assert(t.a[1].x == 42);
  return 0;
}
