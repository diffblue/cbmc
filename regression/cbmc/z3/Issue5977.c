#include <assert.h>

void main()
{
  int i;
  __CPROVER_assume(i % 2 == 0);
  assert(__CPROVER_exists {
    int j;
    i == j + j
  });
}
