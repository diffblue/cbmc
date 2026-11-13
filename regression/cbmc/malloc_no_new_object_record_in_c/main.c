#include <stdlib.h>

// C has no new[] or delete[], so malloc does not record its object for their
// checks (a C program has no C++ code: the library models are preprocessed
// without __CPROVER_CPP_PROGRAM)
extern const void *__CPROVER_new_object;

int main()
{
  void *p = malloc(1);
  __CPROVER_assert(p == NULL || __CPROVER_new_object != p, "not recorded");
  free(p);
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
