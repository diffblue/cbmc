#include <stdbool.h>
int f(int *x) __CPROVER_requires(0 < *x && *x < 10000)
  __CPROVER_ensures(__CPROVER_return_value == *x + 2)
{
  return g(x) + 1;
}

int g(int *x) __CPROVER_requires(0 <= *x && *x <= 10000)
  __CPROVER_ensures(__CPROVER_return_value == *x + 1)
{
  return *x + 1;
}

bool nondet_bool();
int main()
{
  int x;

  // call either f or g
  if(nondet_bool())
    f(&x);
  else
  {
    __CPROVER_assume(0 <= x && x <= 10000);
    g(&x);
  }

  return 0;
}
