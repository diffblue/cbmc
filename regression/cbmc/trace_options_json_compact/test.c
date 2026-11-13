#include <assert.h>

// A function whose parameter-passing and internal steps show up in a full
// trace; with --compact-trace only non-parameter assignments, declarations,
// function calls/returns and the violated assertion remain.
int add(int a, int b)
{
  int result = a + b;
  return result;
}

int main(int argc, char *argv[])
{
  int x = add(argc, 2);
  assert(x == 0);
}
