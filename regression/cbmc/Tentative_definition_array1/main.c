// C standard 6.9.2, paragraph 5: a tentative definition of an array with
// unspecified size becomes a definition with size 1.
// This test verifies that the completed array type is propagated into
// function bodies in the goto program, not just the symbol table.

#include <assert.h>

int A[];

void write_A()
{
  A[0] = 42;
}

int read_A()
{
  return A[0];
}

int main()
{
  write_A();
  int v = read_A();
  assert(v == 42);
  return 0;
}
