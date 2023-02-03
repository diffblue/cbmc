#include <stdlib.h>
#define SIZE 80

void main()
{
  unsigned long len;
  __CPROVER_assume(len <= SIZE);
  __CPROVER_assume(len >= 8);
  const char *i = malloc(len);
  const char *end = i + len;
  char s = 0;

  while(i != end)
  {
    s = *i++;
  }
}
