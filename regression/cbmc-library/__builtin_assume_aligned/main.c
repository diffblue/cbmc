#include <assert.h>

int main()
{
  int x = 5;
  // Per the GCC documentation __builtin_assume_aligned returns its
  // first argument (and asserts nothing at run time).
  void *p = __builtin_assume_aligned(&x, 4);
  assert(p == &x);
  assert(*(int *)p == 5);

  // pointer to const
  const int y = 3;
  const int *r = __builtin_assume_aligned(&y, 4);
  assert(*r == 3);

  // three-argument form (exp, align, misalign), with a false claim: the
  // model must neither prune this path nor report the claim
  char buf[16];
  char *q = __builtin_assume_aligned(buf + 1, 8, 3);
  assert(q == buf + 1);
  __CPROVER_assert(0, "reachable after a false alignment claim");
  return 0;
}
