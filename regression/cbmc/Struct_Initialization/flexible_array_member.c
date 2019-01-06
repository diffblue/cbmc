#include <assert.h>

struct f
{
  int w;
  int x[];
};

struct f f = {4, {0, 1, 2, 3}};

int main()
{
  assert(sizeof(f) == sizeof(int));
  assert(f.x[1] == 1);
  return 0;
}
