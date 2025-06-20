#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));
  __CPROVER_assert(__CPROVER_POINTER_OFFSET(p) == 0, "");
}
