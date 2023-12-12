#include <assert.h>

void main()
{
  int i;
  int *p = &i;
  int j;
  __CPROVER_assume(j == 1 / (*p));
}
