
#include <assert.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  int **pptr;
  int *ptr1 = (int *)malloc(sizeof(int));
  *ptr1 = 1;
  int *ptr2 = (int *)malloc(sizeof(int));
  *ptr2 = 2;

  pptr = (argc == 5 ? &ptr1 : &ptr2);

  assert(**pptr == argc);
}
