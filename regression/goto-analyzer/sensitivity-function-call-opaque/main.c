#include <assert.h>
#define ASSERT(x) __CPROVER_assert((x), "assertion " #x)

int global_value;

int opaque(int other, int* side_effect);

int main(int argc, char *argv[])
{
  int x=3;
  int y=4;

  global_value=4;

  int z=bar(x+1, &y);

  ASSERT(x==3); // Success
  ASSERT(y==4); // Unknown - the opaque function could have modified it
  ASSERT(z==0); // Unknown - the opaque function could have returned anything
  ASSERT(global_value==4); // Unknown - the opaque function could have modified this

  return 0;
}
