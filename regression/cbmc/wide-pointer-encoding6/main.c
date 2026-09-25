// Issue #2117 / assumed pointer equality between reused addresses.
// boolbv_set_equality_to_true forces full-bitvector identity for an assumed
// pointer equality. This must not over-constrain the model to UNSAT when the
// two pointers are distinct dynamic objects whose addresses may be reused
// after free -- the assumption must remain satisfiable.
#include <stdlib.h>

int main()
{
  int *x = malloc(sizeof(int));
  free(x);
  int *y = malloc(sizeof(int));
  __CPROVER_assume(x == y);
  __CPROVER_assert(0, "reachable: assumed address reuse not over-constrained");
}
