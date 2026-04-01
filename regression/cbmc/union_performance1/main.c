// Test that byte_extract from a union does not cause performance explosion.
// See GitHub issue diffblue/cbmc#8813.
#include <assert.h>
#include <stdint.h>

typedef struct
{
  int32_t data[8];
} arr;

int main()
{
  union
  {
    arr a;
    arr b;
  } u;
  unsigned i;
  __CPROVER_assume(i < 8);
  u.a.data[i] = 42;
  assert(u.b.data[i] == 42);
}
