#include <stdlib.h>

struct pair
{
  int x;
  int y;
};

void foo(struct pair *p) __CPROVER_assigns(p->y)
  __CPROVER_ensures((p != NULL) == > (p->y == __CPROVER_old(p->y) + 5))
    __CPROVER_ensures((p == NULL) == > (p->y == __CPROVER_old(p->y)))
{
  if(p != NULL)
    p->y = p->y + 5;
}

int main()
{
  struct pair *p = NULL;
  foo(p);

  return 0;
}
