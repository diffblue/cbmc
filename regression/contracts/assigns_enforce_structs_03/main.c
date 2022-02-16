#include <stdlib.h>

struct pair
{
  int x;
  int y;
};

struct pair_of_pairs
{
  struct pair p1;
  struct pair p2;
};

int f(struct pair *a) __CPROVER_assigns()
{
  struct pair_of_pairs *pop =
    (struct pair_of_pairs *)malloc(sizeof(struct pair_of_pairs));
  a = &(pop->p2);
  a->y = 5;
}

int main()
{
  struct pair m;
  f(&m);

  return 0;
}
