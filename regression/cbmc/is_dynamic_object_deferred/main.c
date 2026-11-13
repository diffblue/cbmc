#include <stdlib.h>
int *nondet_ptr();
int main()
{
  int *p = nondet_ptr();
  _Bool d = __CPROVER_DYNAMIC_OBJECT(p);
  int *q = malloc(sizeof(int));
  // p may alias the malloc result, so d can be true
  __CPROVER_assert(
    !(q && __CPROVER_same_object(p, q)) || d,
    "same object as q implies dynamic");
  return 0;
}
