#include <assert.h>
#include <stdio.h>

int main()
{
  char result[10];
  int bytes = snprintf(result, 10, "%d\n", 42);
  // C11 7.21.6.5: the return value may exceed the buffer size, and the
  // characters actually written are null-terminated
  assert(bytes >= -1);
  if(bytes >= 0)
    assert(result[bytes < 9 ? bytes : 9] == 0);
  return 0;
}
