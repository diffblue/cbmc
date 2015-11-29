#include <assert.h>

// We can't simplify this, even for array_of because we don't know if it is in bounds
// However we can use the CONSTANT_ARRAY_HACK

int array [256 * 256];

int main (void) {
  int index;
  int value = array[index];

  assert(value != 0);

  return 1;
}
