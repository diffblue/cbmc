#include <assert.h>
#include <stdio.h>

int main()
{
  char result[10];
  int bytes = snprintf(result, 10, "%d\n", 42);
  assert(bytes <= 10);
  return 0;
}
