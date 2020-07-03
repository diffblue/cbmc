#include <assert.h>

int nondet_int(void);

int main(int argc, char **argv)
{
  int x = nondet_int();
  int y = nondet_int();

  __CPROVER_assert(1, "1");
  __CPROVER_assert(0 || 1, "0 || 1");
  __CPROVER_assert(1 && 1, "1 && 1");
  __CPROVER_assert(1 || x, "1 || x");
  __CPROVER_assert(y || 1, "y || 1");

  return 0;
}
