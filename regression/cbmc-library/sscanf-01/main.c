#include <assert.h>
#include <stdio.h>

int main()
{
  char dest[10];
  int result = sscanf("hello", "%s", dest);
  assert(result == 1);
  return 0;
}
