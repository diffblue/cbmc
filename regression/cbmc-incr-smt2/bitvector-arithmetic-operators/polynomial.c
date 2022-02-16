#include <stdbool.h>

int main()
{
  int x;
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > -100);
  bool quadratic_solved = (x + 8) * (x - 42) == 0;

  if(x < 0)
    __CPROVER_assert(!quadratic_solved, "No negative solution");
  else
    __CPROVER_assert(!quadratic_solved, "No positive solution");

  return 0;
}
