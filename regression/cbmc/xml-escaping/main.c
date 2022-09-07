#include <assert.h>

int main(void)
{
  __CPROVER_bool x;
  __CPROVER_assume(!x);
  assert(0);
}
