#include <stdlib.h>

int main()
{
  char *p = malloc(100);
  assert(p); // should fail, given the malloc-may-fail option
}
