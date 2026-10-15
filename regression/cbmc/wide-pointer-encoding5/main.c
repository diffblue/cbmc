// Test for --model-stack-layout: stack growth direction,
// adjacent placement, and buffer overflow modeling
#include <stdint.h>
void main()
{
  int a = 1;
  int b = 2;
  int c = 3;

  // Stack growth direction
  __CPROVER_assert((uint64_t)&a > (uint64_t)&b, "a has higher address than b");
  __CPROVER_assert((uint64_t)&b > (uint64_t)&c, "b has higher address than c");

  // Adjacent placement
  __CPROVER_assert(
    (uint64_t)&a - (uint64_t)&b == sizeof(int), "a and b are adjacent");

  // Buffer overflow: writing past a hits b
  char *p = (char *)&a;
  p[sizeof(int)] = 42;
  __CPROVER_assert(*(char *)&b == 42, "overflow from a lands on b");
}
