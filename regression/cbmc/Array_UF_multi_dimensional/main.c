#include <assert.h>

int a[100][100];

int main(void)
{
  unsigned i, k, j1, j2;
  __CPROVER_assume(i < 100 && k < 100 && j1 == i && j2 == k);
  a[i][k] = 5;
  assert(a[j1][j2] == 5);
  return 0;
}
