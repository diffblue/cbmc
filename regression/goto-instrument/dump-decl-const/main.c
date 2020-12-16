#include <assert.h>

struct S
{
  const int x;
  const int y : 8;
  const int *const p;
};

int foo()
{
  return 1;
}

int main()
{
  struct S s1 = {foo(), 1, 0};
  assert(s1.x == 1);
}
