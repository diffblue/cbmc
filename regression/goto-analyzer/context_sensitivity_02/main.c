#include <assert.h>

int negate(int x)
{
  return -x;
}

int main(int argc, char **argv)
{
  int x = 23;
  int nx = negate(x);
  int nnx = negate(nx);

  assert(x == nnx);

  return 0;
}
