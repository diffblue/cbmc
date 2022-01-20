#include <assert.h>

#ifndef __GNUC__
_Bool __atomic_test_and_set(void *, int);
#endif

int main()
{
  char c = 0;
  assert(!__atomic_test_and_set(&c, 0));
  return 0;
}
