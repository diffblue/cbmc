#include <assert.h>

int main(int argc, char *argv[])
{
  int y = 1;
  int z;
  if(y)
  {
    assert(y != 0);
    z = 1;
  }
  else
  {
    assert(y == 0);
    z = 0;
  }
  assert(z == 1);
}
