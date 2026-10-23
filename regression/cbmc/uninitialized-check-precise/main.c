#include <stdlib.h>

void do_init(int *out)
{
  *out = 42;
}

void do_nothing(int *out)
{
}

int main()
{
  // Test 1: interprocedural init — callee writes through pointer
  int x;
  do_init(&x);
  int y = x; // PASS: x initialized by do_init

  // Test 2: interprocedural no-init — callee does NOT write
  int z;
  do_nothing(&z);
  int w = z; // FAIL: z not initialized

  return 0;
}
