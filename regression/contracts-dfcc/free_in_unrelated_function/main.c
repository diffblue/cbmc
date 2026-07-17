#include <stdlib.h>

void foo(void *p)
{
  free(p);
}

int main()
{
  int x = 42;
  return 0;
}
