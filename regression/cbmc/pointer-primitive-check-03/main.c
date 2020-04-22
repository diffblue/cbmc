#include <stdlib.h>

void main()
{
  // uninitialized pointer
  char *p1;
  __CPROVER_POINTER_OBJECT(p1);

  // special value of invalid pointer
  char *p2 = (size_t)1 << (sizeof(char *) * 8 - 8);
  __CPROVER_POINTER_OBJECT(p2);

  // pointer object 123, offset 123, not pointing to valid memory
  char *p3 = ((size_t)123 << (sizeof(char *) * 8 - 8)) | 123;
  __CPROVER_POINTER_OBJECT(p3);

  // negative offset
  char *p4 = malloc(1);
  p4 -= 1;
  __CPROVER_POINTER_OBJECT(p4);

  // offset out of bounds
  char *p5 = malloc(10);
  p5 += 10;
  __CPROVER_POINTER_OBJECT(p5);

  // dead
  char *p6;
  {
    char c;
    p6 = &c;
  }
  __CPROVER_POINTER_OBJECT(p6);
  *p6;

  // deallocated
  char *p7 = malloc(1);
  free(p7);
  __CPROVER_POINTER_OBJECT(p7);
}
