#include <string.h>

struct S
{
  int i;
  int j;
};

int main()
{
  unsigned x;
  char A[x];
  __CPROVER_assume(x == sizeof(int));
  A[0] = 42;
  struct S s;
  s.j = 1;
  memcpy(&s, A, x);
  __CPROVER_assert((s.i & 0xFF) == 42, "lowest byte is 42");
  __CPROVER_assert(s.j == 1, "s.j is unaffected by upate");
}
