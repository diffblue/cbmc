#include <stdlib.h>

_Bool nondet_bool();

int main()
{
  char *s = NULL;
  char A[3];
  _Bool s_is_set = 0;

  if(nondet_bool())
  {
    s = A;
    s_is_set = 1;
  }

  if(s_is_set)
  {
    unsigned len;
    __CPROVER_assume(len < 3);
    s += len;
  }

  if(s)
    *s = 42;

  return 0;
}
