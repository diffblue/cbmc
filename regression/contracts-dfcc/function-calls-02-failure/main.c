#include <stdbool.h>
int f(int *x) __CPROVER_requires(0 <= *x && *x <= 10000)
  __CPROVER_ensures(__CPROVER_return_value == *x + 2)
{
  return g(x) + 1;
}

// preconditions of g are stricter wrt that of f
int g(int *x) __CPROVER_requires(0 < *x && *x < 10000)
  __CPROVER_ensures(__CPROVER_return_value == *x + 1)
{
  // violate the post condition if g is called outside of its preconditions
  if(!(0 < *x && *x < 10000))
    return 0;
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
    g(&x);

  return 0;
}
