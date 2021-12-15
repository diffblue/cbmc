#include <assert.h>
#include <stdlib.h>

// clang-format off
int main() {
  char *a = malloc(1);

  assert(*a == *a);

  // BUG: In https://github.com/diffblue/cbmc/issues/6231, it was reported that
  // no checks would be performed on the derefence inside the quantified statement,
  // even when explicitly requested via for instance `--pointer-check`, because
  // we would simply skip over these quantified statements in goto-check.
  assert(
    __CPROVER_forall {
      int i ; (0 <= i && i < 1) ==> *(a+i) == *(a+i)
    }
  );
}
// clang-format on
