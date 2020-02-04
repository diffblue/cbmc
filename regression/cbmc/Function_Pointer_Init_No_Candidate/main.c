#include <assert.h>

typedef int (*other_function_type)(int n);

void foo(other_function_type other_function)
{
  // returning from the function call is unreachable -> the following assertion
  //   should succeed
  // requesting `pointer-check` will then catch the fact that there is no valid
  //   candidate function to call resulting in an invalid function pointer
  //   failure
  assert(other_function(4) > 5);
}
