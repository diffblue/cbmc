#include <assert.h>

typedef int (*other_function_type)(int n);

void foo(other_function_type other_function)
{
  assert(other_function(4) > 5);
}
