#include <assert.h>
#include <limits.h>
struct pair
{
  int x;
  int y;
};

void foo(struct pair *p) __CPROVER_requires(p)
  __CPROVER_requires(0 <= p->y && p->y < INT_MAX) __CPROVER_assigns(p->y)
    __CPROVER_ensures(p->y == __CPROVER_old(p->y) + 1)
{
  p->y = p->y + 1;
}

int main()
{
  struct pair p;
  __CPROVER_assume(0 <= p.y && p.y < INT_MAX);
  int old_y = p.y;
  foo(&p);
  assert(p.y == old_y + 1);
  return 0;
}
