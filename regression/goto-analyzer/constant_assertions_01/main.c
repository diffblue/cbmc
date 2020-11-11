#include <assert.h>

int nondet_int(void);

int main(int argc, char **argv)
{
  int x = nondet_int();
  int y = nondet_int();

  __CPROVER_assert(0, "0");
  __CPROVER_assert(0 && 1, "0 && 1");
  __CPROVER_assert(0 || 0, "0 || 0");
  __CPROVER_assert(0 && x, "0 && x");
  __CPROVER_assert(y && 0, "y && 0");

  return 0;
}
