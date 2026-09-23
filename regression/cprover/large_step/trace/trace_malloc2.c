#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int) * 1000);

  p[10] = 1;
  p[10]++;

  __CPROVER_assert(0, "property 1");
}
