#include <stdlib.h>

int main()
{
  if(sizeof(void *) != 8)
    return 0;

  char *p = malloc(1);
  if(p == 0)
    return 0;

  if(
    (unsigned long)p >
    42) // unsoundly evaluates to true due to pointer encoding
  {
    return 0;
  }

  __CPROVER_assert(0, "");

  return 0;
}
