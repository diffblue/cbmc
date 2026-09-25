#include <assert.h>

int main()
{
  int x = 5;
  // Per the GCC documentation __builtin_assume_aligned returns its
  // first argument (and asserts nothing at run time).
  void *p = __builtin_assume_aligned(&x, 4);
  assert(p == &x);
  assert(*(int *)p == 5);
  return 0;
}
