#include <stdlib.h>

int nondet_int(void);

int main()
{
  int *q = malloc(sizeof(int));
  __CPROVER_assume(q != NULL);

  int *p;

  if(nondet_int())
  {
    p = NULL; // NULL on this path
  }
  else
  {
    p = q;
    int a = *p; // valid here -- caches a "p is valid" assertion
  }

  int b = *p; // merge point: on the NULL path this must still be checked

  return b;
}
