#include <assert.h>
#include <string.h>

int main()
{
  char foo[1];
  char result = 0;
  int size;
  __CPROVER_assume(size == 1);

  memset(&result, 42, size);
  __CPROVER_assert(result == 42, "should succeed");
  result = 42;
  memcpy(&result, foo, size);
  __CPROVER_assert(result == 42, "should fail");
}
