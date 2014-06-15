#include <assert.h>
#include <math.h>

int main (int argc, char **argv) {
  float f = -0x1p-129f;
  float g =  0x1p-129f;
  float target = 0x0;

  float result = f + g;

  assert(result == target && signbit(result) == signbit(target));

  return 0;
}
