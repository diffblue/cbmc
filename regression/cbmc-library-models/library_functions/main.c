#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main()
{
  char *p = malloc(4);
  if(p == 0)
    return 0;
  memcpy(p, "abc", 4);
  __CPROVER_assert(strlen(p) == 3, "strlen of the copy");
  char b[8];
  int n = snprintf(b, sizeof(b), "%d", 42);
  __CPROVER_assert(n == 2 && b[0] == '4' && b[1] == '2', "snprintf");
  free(p);
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
