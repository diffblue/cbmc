#include <assert.h>

int main()
{
  int k = __VERIFIER_nondet_int();

  __CPROVER_assume(__CPROVER_exists {
    int i;
    i > 0 && __CPROVER_exists
    {
      int j;
      j > i &&j < k
    }
  });

  assert(k >= 3);

  return 0;
}
