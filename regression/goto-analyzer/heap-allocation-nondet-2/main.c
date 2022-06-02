#include <stdlib.h>

int main()
{
  int *p = malloc(10);
  if(nondet())
    ++p;
}
