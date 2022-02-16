#include <stdlib.h>

struct pair
{
  int x;
  int y;
};

int f(int *a) __CPROVER_assigns()
{
  struct pair *p = (struct pair *)malloc(sizeof(struct pair));
  a = &(p->y);
  *a = 5;
}

int main()
{
  int m = 4;
  f(&m);

  return 0;
}
