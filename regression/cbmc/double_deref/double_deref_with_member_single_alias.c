
#include <assert.h>
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

  assert(*(cptr->iptr) == argc);
}
