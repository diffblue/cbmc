#include <assert.h>
#include <stdlib.h>

// Similar to the previous tests in forall_6231_1 but this one aims to check
// the antecedent of the forall expression to make sure that checks are being
// generated correctly for it.

// clang-format off
int main() {
  char *a = malloc(10);
  int n;

  // BUG: In https://github.com/diffblue/cbmc/issues/6231, it was reported that
  // no checks would be performed on the derefence inside the quantified statement,
  // even when explicitly requested via for instance `--pointer-check`, because
  // we would simply skip over these quantified statements in goto-check.
  assert(
    __CPROVER_forall {
      int i ; (0 <= i && i < (n / 0))  /* (n / 0) should be caught by --div-by-zero-check */
      ==> *(a+i) == *(a+i)
    }
  );
}
// clang-format on
