#include <stdlib.h>

int main(int argc, char **argv)
{
  void **pptr;
  int *ptr1 = (int *)malloc(sizeof(int));
  *ptr1 = 1;

  pptr = &ptr1;

  __CPROVER_assert(*(int *)*pptr == argc, "assertion *(int *)*pptr == argc");
}
