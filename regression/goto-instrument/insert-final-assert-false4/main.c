#include <stdlib.h>

int nondet_int();
int main()
{
  if(nondet_int())
  {
    __CPROVER_assume(0 == 1);
    return 0;
  }
  else
  {
    return 1;
  }
}
