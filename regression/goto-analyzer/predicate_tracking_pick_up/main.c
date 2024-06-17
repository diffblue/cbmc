#include <assert.h>

int nondet_int(void);

int main(int argc, char **argv)
{
  int x = nondet_int();
  int y = nondet_int();
  int z = nondet_int();

  // Test whether predicates are picked up at all
  if(x < y)
  {
    __CPROVER_assert(x < y, "Direct syntactic match");
  }

  // Check whether they are pruned on merge
  __CPROVER_assert(x < y, "Should be unknown as pruned");

  if(x < y)
  {
    if(!(x < y))
    {
      __CPROVER_assert(0, "Safe as unreachable");
    }

    __CPROVER_assert(x < y, "Preserved after merge with bottom");

    __CPROVER_assert(y > x, "Safe using context-free simplification");

    z = 0;

    __CPROVER_assert(x < y + z, "Safe using context-dependent simplification");
  }

  return 0;
}
