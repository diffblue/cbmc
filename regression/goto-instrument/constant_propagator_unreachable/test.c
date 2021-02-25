#include <assert.h>

void unreachable(void)
{
  int x = 0;
  assert(x != 0);
}

int main(void)
{
  return 0;
}
