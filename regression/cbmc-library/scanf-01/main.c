#include <assert.h>
#include <stdio.h>

int main()
{
  scanf(""); // parse nothing, must not result in any out-of-bounds access
  int x = 0;
  scanf("%d", &x);
  _Bool nondet;
  if(nondet)
    __CPROVER_assert(x == 0, "need not remain zero");
  else
    __CPROVER_assert(x != 0, "may remain zero");
  long int lx = 0;
  long long int llx = 0;
  scanf("%d, %ld, %lld", &x, &lx, &llx);
  if(nondet)
    __CPROVER_assert(lx + llx == 0, "need not remain zero");
  else
    __CPROVER_assert(lx + llx != 0, "may remain zero");
  return 0;
}
