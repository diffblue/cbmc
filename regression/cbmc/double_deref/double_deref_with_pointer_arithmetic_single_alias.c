
#include <assert.h>
#include <stdlib.h>

struct container
{
  int *iptr;
};

int main(int argc, char **argv)
{
  int **new_ptrs = malloc(2 * sizeof(int *));
  int *iptr1 = (int *)malloc(sizeof(int));
  *iptr1 = 1;

  new_ptrs[argc % 2] = iptr1;

  assert(*(new_ptrs[argc % 2]) == argc);
}
