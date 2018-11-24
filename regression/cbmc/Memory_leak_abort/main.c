#include <stdlib.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main()
{
  int *p = malloc(sizeof(int));
  if(*p == 0)
    abort();
  if(*p == 1)
    exit(1);
  if(*p == 2)
    _Exit(1);
  free(p);
  return 0;
}
