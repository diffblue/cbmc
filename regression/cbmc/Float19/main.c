#include <assert.h>
#include <math.h>

void f00 (float f) {
  if (f > 0x1.FFFFFEp+127) {
    assert(isinf(f));
  }
}

int main (void) {
  float f;

  f00(f);

  return 0;
}
