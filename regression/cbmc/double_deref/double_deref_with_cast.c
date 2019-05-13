
#include <assert.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  void **pptr;
  int *ptr1 = (int *)malloc(sizeof(int));
  *ptr1 = 1;
  int *ptr2 = (int *)malloc(sizeof(int));
  *ptr2 = 2;

  pptr = (argc == 1 ? &ptr1 : &ptr2);

  assert(*(int *)*pptr == argc);
}
