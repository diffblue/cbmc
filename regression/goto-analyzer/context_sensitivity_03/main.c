#include <assert.h>

int step(int x)
{
  if(x <= 0)
  {
    return 0;
  }
  else
  {
    return x + step(x - 1);
  }
}

int main(int argc, char **argv)
{
  int x = 5;
  int res = step(x);

  assert(res == 15);

  return 0;
}
