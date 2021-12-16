#include <assert.h>
#include <stdlib.h>

struct pair
{
  int x;
  int *y;
};

int z = 5;
int w[10] = {0};

void foo(struct pair *p) __CPROVER_assigns(*(p->y), z)
  __CPROVER_ensures(*(p->y) == __CPROVER_old(*(p->y)) + __CPROVER_old(z))
{
  *(p->y) = *(p->y) + z;
  z = 10;
}

void bar(struct pair *p) __CPROVER_assigns(p->y)
  __CPROVER_ensures(p->y == __CPROVER_old(p->y) + 5)
{
  p->y = (p->y + 5);
}

void baz(struct pair p) __CPROVER_assigns()
  __CPROVER_ensures(p == __CPROVER_old(p))
{
  struct pair pp = p;
  struct pair empty = {0};
  p = empty;
  p = pp;
}

int main()
{
  struct pair *p = malloc(sizeof(*p));
  p->y = malloc(sizeof(*(p->y)));
  p->x = 2;
  *(p->y) = 2;
  foo(p);
  assert(*(p->y) == 7);
  p->y = w;
  w[5] = -1;
  bar(p);
  assert(*(p->y) == -1);
  baz(*p);

  return 0;
}
