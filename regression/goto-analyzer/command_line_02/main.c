#include <assert.h>

int f00(int x)
{
  assert(x != 0);
  return 0;
}

int main(int argc, char **argv)
{
  int v = 0;
  v = f00(v);
  assert(v != 0);

  return 0;
}
