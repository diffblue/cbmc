#include <assert.h>

int main(void)
{
  unsigned n, i, k, j1, j2;
  __CPROVER_assume(n > 0 && n < 100 && i < 7 && k < n && j1 == i && j2 == k);
  int a[7][n];
  a[i][k] = 5;
  assert(a[j1][j2] == 5);
  return 0;
}
