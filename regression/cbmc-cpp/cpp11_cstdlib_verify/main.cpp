// Verify abs() from <cstdlib>
#include <cassert>
#include <cstdlib>

int nondet_int();

int main()
{
  int x = nondet_int();
  __CPROVER_assume(x > -100 && x < 100 && x != 0);

  int a = abs(x);
  assert(a > 0);
  assert(a <= 99);

  return 0;
}
