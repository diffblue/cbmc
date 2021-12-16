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

int f(int *a) __CPROVER_assigns()
{
  struct pair_of_pairs *pop =
    (struct pair_of_pairs *)malloc(sizeof(struct pair_of_pairs));
  a = &(pop->p2.x);
  *a = 5;
}

int main()
{
  int m = 4;
  f(&m);

  return 0;
}
