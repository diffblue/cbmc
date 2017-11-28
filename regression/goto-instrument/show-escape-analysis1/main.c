#include <stdlib.h>

void foo()
{
  int *leaked1=malloc(sizeof(int));
  int *leaked2=malloc(sizeof(int));
}

int main()
{
  foo();
  return 0;
}
