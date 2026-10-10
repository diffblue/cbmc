#include <stdlib.h>

int *p;
void **p_ptr;

int main()
{
  p = malloc(1);
  p_ptr = &p;
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(*p_ptr), "property 1");
  return 0;
}
