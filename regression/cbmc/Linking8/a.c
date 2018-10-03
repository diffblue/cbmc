#include <stdlib.h>

void foo();

int main()
{
  extern void *p;
  p = malloc(sizeof(int));
  foo();
  return 0;
}
