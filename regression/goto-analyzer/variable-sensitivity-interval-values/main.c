#include <assert.h>

int main(void)
{
  int x = 0;
  int zero = x;
  int nondet_condition;
  if(nondet_condition)
  {
    x = 1;
    int one = x;
  }
  else
  {
    x = -1;
    int minus_one = x;
  }
  int between_minus_one_and_one = x;
  x = 13;
  int thirteen = x;
  return 0;
}
