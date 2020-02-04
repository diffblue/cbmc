#include <assert.h>

int identity(int n)
{
  return n;
}
int increment(int n)
{
  return n + 1;
}

typedef int (*other_function_type)(int n);

void foo(other_function_type other_function)
{
  // the following assertion is reachable and should fail (because of the identity case)
  assert(other_function(4) == 5);
  // the following assertion should succeed (satisfied by both candidates)
  assert(other_function(4) >= 4);
}

int main()
{
  foo(&identity);
  foo(&increment);
  return 0;
}
