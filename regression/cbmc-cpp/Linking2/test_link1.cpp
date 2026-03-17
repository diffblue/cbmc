#include <assert.h>

extern "C" int x;
extern "C" int f(void);

int main()
{
  int z;

  x = z;
  assert(f() == z);
}
