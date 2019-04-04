#include <assert.h>

struct S
{
  int a;
};

int main()
{
  struct S s;
  s.a = 1;

  assert(s.a == 1);

  int A[1];
  A[0] = 1;

  assert(A[0] == 1);

  return 0;
}
