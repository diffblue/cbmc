#include <assert.h>

int main()
{
  char c = 0;
  assert(!__atomic_test_and_set(&c, 0));
  return 0;
}
