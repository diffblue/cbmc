#include <assert.h>

struct pair
{
  int x[3];
  int y;
};

int f1(struct pair *p) __CPROVER_assigns(p->x)
{
  p->y = 2;
  p->x[0] = 0;
  p->x[1] = 1;
  p->x[2] = 2;
  return 0;
}

int main()
{
  struct pair p = {0};
  f1(&p);
  assert(p.y == 2);
  assert(p.x[0] == 0);
  assert(p.x[1] == 1);
  assert(p.x[2] == 2);
  return 0;
}
