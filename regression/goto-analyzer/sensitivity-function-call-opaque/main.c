#include <assert.h>

int opaque(int other, int* side_effect);

int main(int argc, char *argv[])
{
  int x=3;
  int y=4;
  int z=bar(x+1, &y);

  assert(x==3); // Success
  assert(y==4); // Unknown - the opaque function could have modified it
  assert(z==0); // Unknown - the opaque function could have returned anything

  return 0;
}
