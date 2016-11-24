#include <assert.h>

int main()
{
#if defined(__GNUC__) && !defined(__clang__)
  // accepted by GCC, but not Clang
  assert(0 < 50.0d);

  assert(0 < 1.0w);
  assert(0 < 1.0q);
  assert(0 < 1.0W);
  assert(0 < 1.0Q);

  assert(0 < 1.0df);
  assert(0 < 1.0dd);
  assert(0 < 1.0dl);

#endif

  return 0;
}
