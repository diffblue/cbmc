#include <assert.h>
#include <stdlib.h>

// Similar to our test in `test.c` of this folder, with the difference being
// that the malloc size is less than the bound checked, which implies that the
// check for the pointer being outside the object bounds is expected to fail.

// clang-format off
int main() {
  char *a = malloc(4);

  assert(*a == *a);

  // BUG: no errors even with `--pointer-check` enabled -- now fixed.
  assert(
    __CPROVER_forall {
      int i ; (0 <= i && i < 10) ==> *(a+i) == *(a+i)
    }
  );
}
// clang-format on
