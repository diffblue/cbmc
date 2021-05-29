#include <assert.h>

int global_value;

int opaque(int other, int *side_effect);

int main()
{
  int x = 3;
  int y = 4;

  global_value = 4;

  int z = bar(x + 1, &y);

  assert(x == 3); // Success
  assert(y == 4); // Unknown - the opaque function could have modified it
  assert(z == 0); // Unknown - the opaque function could have returned anything
  assert(
    global_value ==
    4); // Unknown - the opaque function could have modified this

  return 0;
}
