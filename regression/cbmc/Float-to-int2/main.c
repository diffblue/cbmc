#include <assert.h>

int nondet_int();
double nondet_double();

int main(void)
{
  int i = nondet_int();
  double di = (double)i;
  int j = (int)di;

  assert(i == j);

  return 0;
}

