#include <stdlib.h>

void main()
{
  // uninitialized pointer
  char *p1;
  __CPROVER_r_ok(p1, 1);

  // special value of invalid pointer
  char *p2 = (size_t)1 << (sizeof(char *) * 8 - 8);
  __CPROVER_r_ok(p2, 1);

  // pointer object 123, offset 123, not pointing to valid memory
  char *p3 = ((size_t)123 << (sizeof(char *) * 8 - 8)) | 123;
  __CPROVER_r_ok(p3, 1);

  // negative offset
  char *p4 = malloc(1);
  p4 -= 1;
  __CPROVER_r_ok(p4, 1);

  // offset out of bounds
  char *p5 = malloc(10);
  p5 += 10;
  __CPROVER_r_ok(p5, 1);

  // dead
  char *p6;
  {
    char c;
    p6 = &c;
  }
  __CPROVER_r_ok(p6, 1);
  *p6;

  // deallocated
  char *p7 = malloc(1);
  free(p7);
  __CPROVER_r_ok(p7, 1);
}
