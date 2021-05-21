#include <stdlib.h>

struct container
{
  int *iptr;
};

int main(int argc, char **argv)
{
  struct container *cptr;
  struct container container1;
  container1.iptr = (int *)malloc(sizeof(int));
  *container1.iptr = 1;

  cptr = &container1;

  __CPROVER_assert(*(cptr->iptr) == argc, "assertion *(cptr->iptr) == argc");
}
