#include <assert.h>
typedef struct test
{
  int id;
} test;

int main()
{
  int r, s = 1;
  __CPROVER_assume(r >= 0);
  while(r > 0)
    // clang-format off
    __CPROVER_loop_invariant(r >= 0 && s == 1)
    __CPROVER_decreases(r)
    // clang-format on
    {
      s = 1;
      goto label_1;

      if(1 == 1)
        goto label_0;

      test newAlloc0 = {0};

      if(1 == 1)
        goto label_1;

    label_0:
      r--;

    label_1:
      r--;
    }
  assert(r == 0);
  assert(s == 1);

  return 0;
}
