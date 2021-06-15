#include <assert.h>

int bar(int other)
{
  assert(other == 4);
  return other + 1;
}

int main()
{
  int x = 3;
  int y = bar(x + 1);
  assert(y == 5);
}
