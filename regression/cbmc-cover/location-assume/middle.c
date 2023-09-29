#include <assert.h>

int main()
{
  int i;
  int j;
  j = i;
  __CPROVER_assume(0);
  j = i + 2;
  return 0;
}
