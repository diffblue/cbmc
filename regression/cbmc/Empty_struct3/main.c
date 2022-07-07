#include <assert.h>

struct Unit
{
};

int main()
{
  struct Unit var_0;
  int x;
  int y = x;
  assert(0);
  assert(y == x);
  return 0;
}
