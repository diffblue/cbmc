
#include <assert.h>
#include <stdlib.h>

struct container
{
  int *iptr;
};

int main(int argc, char **argv)
{
  struct container *cptr;
  struct container container1, container2;
  container1.iptr = (int *)malloc(sizeof(int));
  *container1.iptr = 1;
  container2.iptr = (int *)malloc(sizeof(int));
  *container2.iptr = 2;

  cptr = (argc == 1 ? &container1 : &container2);

  assert(*(cptr->iptr) == argc);
}
