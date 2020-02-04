#include <assert.h>

int identity(int n)
{
  return n;
}

typedef int (*other_function_type)(int n);

void foo(other_function_type other_function)
{
  // the following assertion is reachable and should fail (the only candidate is identity)
  assert(other_function(4) == 5);
  // the following assertion should succeed
  assert(other_function(4) == 4);
}

int main()
{
  foo(&identity);
  return 0;
}
