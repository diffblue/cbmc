#include <stdlib.h>
#define SIZE 80

void main()
{
  unsigned long len;
  __CPROVER_assume(len <= SIZE);
  __CPROVER_assume(len >= 8);
  char *array = malloc(len);
  __CPROVER_assume(array != 0);

  unsigned i = 0;

  while(i <= len - 2)
  {
    i++;
  }
  unsigned result = array[i];
}
