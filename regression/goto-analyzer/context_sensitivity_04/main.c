#include <assert.h>

int step(int x)
{
  if(x == 0)
  {
    assert(x == 0);
    return 0;
  }
  else
  {
    return step(x - 1);
  }
}

int main(int argc, char **argv)
{
  int orig = 20;
  int res = step(orig);

  assert(res == 0);

  return 0;
}
