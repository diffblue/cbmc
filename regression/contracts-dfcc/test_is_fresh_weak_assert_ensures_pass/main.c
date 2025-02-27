#include <stdlib.h>
int nondet_int();

void foo(int *a, int **b_out, int **c_out)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(a, 2*sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b_out, sizeof(int*)))
__CPROVER_requires(__CPROVER_is_fresh(c_out, sizeof(int*)))
__CPROVER_ensures(__CPROVER_is_fresh(*b_out, sizeof(int)))
__CPROVER_ensures(__CPROVER_is_fresh(*c_out, sizeof(int)))
__CPROVER_assigns(*b_out, *c_out)
__CPROVER_ensures(**b_out == a[0])
__CPROVER_ensures(**c_out == a[1])
// clang-format on
{
  if(nondet_int())
  {
    *b_out = malloc(sizeof(int));
    __CPROVER_assume(*b_out != NULL);
    *c_out = malloc(sizeof(int));
    __CPROVER_assume(*c_out != NULL);
  }
  else
  {
    *b_out = malloc(2 * sizeof(int));
    __CPROVER_assume(*b_out != NULL);
    *c_out = *b_out + 1;
  }
  **b_out = a[0];
  **c_out = a[1];
}

int main()
{
  int *a, **b_out, **c_out;
  foo(a, b_out, c_out);
}
