#include <assert.h>

int main(void)
{
  float x = 0.0f;
  float zero = x;
  int nondet_condition;
  if(nondet_condition)
  {
    x = 1.0f;
    float one = x;
  }
  else
  {
    x = -1.0f;
    float minus_one = x;
  }
  float between_minus_one_and_one = x;
  x = 13.0f;
  float thirteen = x;
  return 0;
}
