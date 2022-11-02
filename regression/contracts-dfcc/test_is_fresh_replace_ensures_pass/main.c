#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#define SIZE 10

void foo(char **out_ptr1, char **out_ptr2)
  // clang-format off
  __CPROVER_assigns(*out_ptr1, *out_ptr2)
  __CPROVER_ensures(__CPROVER_is_fresh(*out_ptr1, SIZE))
  __CPROVER_ensures(__CPROVER_is_fresh(*out_ptr2, SIZE))
// clang-format on
{
  *out_ptr1 = malloc(SIZE);
  *out_ptr2 = malloc(SIZE);
}

int main()
{
  char *out1;
  char *out2;
  foo(&out1, &out2);
  __CPROVER_assert(__CPROVER_rw_ok(out1, SIZE), "out1 is rw_ok");
  __CPROVER_assert(__CPROVER_rw_ok(out2, SIZE), "out2 is rw_ok");
  __CPROVER_assert(
    !__CPROVER_same_object(out1, out2), "out1 and out2 are not aliased");
  return 0;
}
