#include <assert.h>

int nondet_int (void);

int main (int argc, char **argv)
{
  int x = nondet_int();
  int y = nondet_int();

  assert(1);
  assert(0 || 1);
  assert(1 && 1);
  assert(1 || x);
  assert(y || 1);

  return 0;
}
