#include <assert.h>

struct a
{
  int x;
};
struct b
{
  struct a p;
  int y;
};

int f00(struct a *ptr)
{
  return ptr->x;
}

int main()
{
  struct b z = {{1}, 2};

  assert(&z == &(z.p));
  assert(&z == &(z.p.x));

  assert(f00(&z) == z.p.x);

  return 0;
}
