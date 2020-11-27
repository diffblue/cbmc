#include <stdlib.h>

int main()
{
  int *ptr = malloc(sizeof(*ptr));
  int a;

  a = *ptr;

  if(ptr == NULL)
    a = 1;

  return 0;
}
