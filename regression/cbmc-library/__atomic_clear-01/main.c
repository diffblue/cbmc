#include <assert.h>

int main()
{
  _Bool n;
  __atomic_clear(&n, 0);
  assert(0);
  return 0;
}
