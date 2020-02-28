#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p;
  int choice;

  if(choice)
  {
    p = malloc(2);
  }
  else
  {
    p = malloc(3);
  }

  assert(__CPROVER_r_ok(p, 2));
  assert(!__CPROVER_r_ok(p, 2));

  assert(__CPROVER_r_ok(p, 3));
  assert(!__CPROVER_r_ok(p, 3));

  assert(__CPROVER_r_ok(p, 4));
  assert(!__CPROVER_r_ok(p, 4));
}
