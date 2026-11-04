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
    z = nondet_int();
    __CPROVER_assert(x < y, "Unrelated assignment does not invalidate");

    y++;
    __CPROVER_assert(x < y, "Relevant assignment does invalidate");
  }

  while(x == y)
  {
    __CPROVER_assert(x == y, "Predicate preserved by loop");
    ++x;
    ++y;
    __CPROVER_assert(x == y, "Predicate true but not lost");
  }

  __CPROVER_assert(x != y, "Infinite loop exit condition");

  return 0;
}
