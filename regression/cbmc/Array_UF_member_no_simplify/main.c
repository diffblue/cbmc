#include <assert.h>

struct S
{
  int x;
  int a[1000];
};

struct S s;

int main(void)
{
  unsigned k, j;
  __CPROVER_assume(k < 1000 && j == k);
  s.a[k] = 5;
  assert(s.a[j] == 5);
  return 0;
}
