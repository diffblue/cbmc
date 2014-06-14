#include <assert.h>

int some_function()
{
  // this will not be executed
  assert(0);
}

int main()
{
  // http://msdn.microsoft.com/en-us/library/s6btaxcs%28v=vs.80%29.aspx
  // the arguments of __noop are _not_ evaluated
  
  __noop(some_function());
}
