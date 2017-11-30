#include <assert.h>

int nondet_int (void);

int main (int argc, char **argv)
{
  int a = 1;
  int b = 2;
  int x = nondet_int();
  int y = nondet_int();

  if (a == b)
    assert(0);  // Trivial false

  if (a == b)
    assert(1);  // Trivial true

  if (a == b)
    assert(x == y); // Undetermined

  if (a == b)
    assert(!(x == y) || (x + 1 + a == b + y));  // Non-trivial true

  if (a == b)
    assert(!(!(x == y) || (x + 1 + a == b + y)));  // Non-trivial false

  return 0;
}
