#include <assert.h>

void f00(int x, int y)
{
  assert(x == 0); // Safe even in location-insensitive

  int z = 23;
  z = x;

  assert(z == 0); // Needs location sensitivity

  assert(y == 23 || y == 42); // Needs context sensitivity
}

int main(int argc, char **argv)
{
  f00(0, 23);

  f00(0, 42);

  return 0;
}
