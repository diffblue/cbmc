#include <stdlib.h>

struct pair
{
  int *x;
  int *y;
};

void foo(struct pair p) __CPROVER_assigns(*(p.y))
  __CPROVER_ensures(*(p.y) == __CPROVER_old(*(p.y)) + 5)
{
  *(p.y) = *(p.y) + 5;
}

int main()
{
  struct pair p;
  p.x = malloc(sizeof(int));
  p.y = malloc(sizeof(int));

  foo(p);

  return 0;
}
