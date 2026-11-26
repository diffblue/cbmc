#include <stdlib.h>

_Bool nondet_bool(void);

int main()
{
  // An untyped allocation, which CBMC models as an unsigned char array.
  unsigned char *obj = malloc(64);
  if(obj == NULL)
    return 0;

  void *target = malloc(32);
  if(target == NULL)
    return 0;

  // Store a pointer that may be NULL; its bytes are zero in that case.
  *(void **)obj = nondet_bool() ? target : NULL;

  // Read the pointer back from those bytes and store through it.
  void **p = *(void ***)obj;
  if(p != NULL)
    *p = NULL;

  return 0;
}
