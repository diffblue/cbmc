#include <assert.h>
#include <stdlib.h>

// This is essentially the same file as in test `forall_6231_1`, with the difference
// being that the forall statement contains a bigger bound, so that we are to have
// more concrete instantiations of the bound variable.

// clang-format off
int main() {
  char *a = malloc(10);

  assert(*a == *a);

  // BUG: In https://github.com/diffblue/cbmc/issues/6231, it was reported that
  // no checks would be performed on the derefence inside the quantified statement,
  // even when explicitly requested via for instance `--pointer-check`, because
  // we would simply skip over these quantified statements in goto-check.
  assert(
    __CPROVER_forall {
      int i ; (0 <= i && i < 10) ==> *(a+i) == *(a+i)
    }
  );
}
// clang-format on
