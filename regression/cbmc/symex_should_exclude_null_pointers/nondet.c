#include <stdlib.h>

struct S
{
  int *p;
  int x;
};

int main()
{
  struct S *s = malloc(sizeof(struct S));
  // Guard must not be removed (deemed trivially true) by try_filter_value_sets.
  if(s->p != NULL)
    __CPROVER_assert(s->p != NULL, "cannot be NULL");
}
