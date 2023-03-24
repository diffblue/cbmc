#include <assert.h>
#include <stdlib.h>

static int adder(const int *a, const int *b)
{
  return (*a + *b);
}

int main()
{
  int x = 1024;

  int (*local_adder)(const int *, const int *) = adder;

  while(x > 0)
    __CPROVER_loop_invariant(1 == 1)
    {
      x += local_adder(&x, &x); // loop detection fails
      //x += adder(&x, &x);       // works fine
    }
}
