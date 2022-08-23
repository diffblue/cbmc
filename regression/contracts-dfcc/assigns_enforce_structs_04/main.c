#include <assert.h>
#include <stdlib.h>

struct pair
{
  int x;
  int y;
};

void f1(struct pair *p) __CPROVER_assigns(p->x)
{
  p->y = 2;
}

void f2(struct pair *p) __CPROVER_assigns(p->y)
{
  p->x = 2;
}

void f3(struct pair *p) __CPROVER_assigns(p->y)
{
  p->y = 0;
}

void f4(struct pair *p) __CPROVER_assigns(*p)
{
  p = NULL;
}

int main()
{
  struct pair p = {0};
  f1(&p);
  f2(&p);
  assert(p.y == 2);
  assert(p.x == 2);
  f3(&p);
  assert(p.y == 0);
  f4(&p);
  return 0;
}
