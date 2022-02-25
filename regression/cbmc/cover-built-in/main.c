#include <stdbool.h>
int main()
{
  int x;
  __CPROVER_assume(-10 <= x & x <= 10);
  int y = x * x * x;
  if(x > 0)
  {
    __CPROVER_cover(y > 900, "y>9000");
  }
  else if(x == 0)
  {
    __CPROVER_assert(y == 0, "y==0");
  }
  else if(x < 0)
  {
    __CPROVER_cover(y < 12, "x<12");
    __CPROVER_cover(true, "reachablility check");
    __CPROVER_cover(
      false, "reachablility check with trivially false condition");
    // reachable in the control-flow but failed because of path constraints
    __CPROVER_cover(y > 12, "x>12");
  }
  else if(x > 10)
  {
    // unreachable
    __CPROVER_cover(true, "reachability check");
    __CPROVER_cover(
      false, "reachablility check with trivially false condition");
    // vacuously proved
    assert(y == 12);
  }
  return 0;
}
