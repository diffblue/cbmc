#include <stdlib.h>

int *p, *q;
void **p_ptr;

int main()
{
  p = malloc(1);
  p_ptr = &p;
  q = malloc(2);
  free(*p_ptr);
  return 0;
}
