
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
  int *iptr2 = (int *)malloc(sizeof(int));
  *iptr2 = 2;

  new_ptrs[argc % 2] = iptr1;
  new_ptrs[1 - (argc % 2)] = iptr2;

  assert(*(new_ptrs[argc % 2]) == argc);
}
