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

int f1(int *a, struct pair *b);

int f1(int *a, struct pair *b) __CPROVER_assigns(*a)
{
  struct pair_of_pairs *pop =
    (struct pair_of_pairs *)malloc(sizeof(struct pair_of_pairs));
  b = &(pop->p2);
  b->y = 5;
}
