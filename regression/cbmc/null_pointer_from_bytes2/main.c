#include <stdlib.h>
#include <string.h>

_Bool nondet_bool(void);

int main()
{
  unsigned char *obj = malloc(16);
  if(obj == NULL)
    return 0;
  int *target = malloc(sizeof(int));
  if(target == NULL)
    return 0;

  // A pointer that may be NULL, stored into and read back from bytes.
  *(int **)obj = nondet_bool() ? target : NULL;
  int *p = *(int **)obj;
  __CPROVER_assert(p == target || p == NULL, "p is target or NULL");
  if(p != NULL)
    *p = 1;

  // Zeroed memory read back as a pointer is NULL.
  memset(obj, 0, 16);
  int *q = *(int **)obj;
  __CPROVER_assert(q == NULL, "q is NULL");

  // A pointer with its lowest byte overwritten by zero still points to target.
  *(int **)obj = target;
  obj[0] = 0;
  int *r = *(int **)obj;
  *r = 3;

  // Dereferencing p without a null check must still be flagged.
  *p = 2;

  return 0;
}
