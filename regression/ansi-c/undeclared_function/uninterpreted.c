#include <assert.h>

int main()
{
  int x;
  assert(__CPROVER_uninterpreted_fn(x) == __CPROVER_uninterpreted_fn(x));
  return 0;
}

int __CPROVER_uninterpreted_fn(int x);
