#include <stdlib.h>

int nondet_int();
int main()
{
  if(nondet_int())
  {
    return 0;
  }
  else
  {
    return 1;
  }
}
