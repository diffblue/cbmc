#include <assert.h>

// Mutually-referential static address constants: a's initializer takes the
// address of b and b's initializer takes the address of a. This is valid C
// and forms a dependency cycle for static initialization. CBMC must break the
// cycle (the chosen order is not semantically significant here) and initialize
// both objects, rather than crashing or leaving a pointer uninitialized.

extern int *b;
int *a = (int *)&b;
int *b = (int *)&a;

int main()
{
  assert(a == (int *)&b);
  assert(b == (int *)&a);
  return 0;
}
