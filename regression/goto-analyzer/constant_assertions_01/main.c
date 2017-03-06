#include <assert.h>

int nondet_int (void);

int main (int argc, char **argv)
{
  int x = nondet_int();
  int y = nondet_int();

  assert(0);
  assert(0 && 1);
  assert(0 || 0);
  assert(0 && x);
  assert(y && 0);

  return 0;
}
