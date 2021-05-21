#include <stdlib.h>

int main(int argc, char **argv)
{
  int **pptr;
  int *ptr1 = (int *)malloc(sizeof(int));
  *ptr1 = 1;

  pptr = &ptr1;

  __CPROVER_assert(**pptr == argc, "assertion **pptr == argc");
}
