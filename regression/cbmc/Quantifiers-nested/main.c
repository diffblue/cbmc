#include <assert.h>

// Nested quantifiers: the body of the outer forall contains an inner forall
// that references the outer quantifier's bound variable `i`. This exercises the
// nested-scope handling in the incremental SMT2 backend's dependency gathering,
// where `i` must be treated as bound (and hence not emitted as a top-level
// declaration) within the inner quantifier's body.
int main()
{
  int b[2][2];
  // clang-format off
  __CPROVER_assume(__CPROVER_forall {
    int i;
    (i >= 0 && i < 2) ==>
      (__CPROVER_forall {
        int j;
        (j >= 0 && j < 2) ==> b[i][j] == i + j
      })
  });
  // clang-format on
  assert(b[0][0] == 0);
  assert(b[0][1] == 1);
  assert(b[1][0] == 1);
  assert(b[1][1] == 2);
  return 0;
}
