#include <assert.h>

int main() {
  __CPROVER_fixedbv[64][32] x;
  int y;

  x=2;
  x -= (__CPROVER_fixedbv[64][32])0.6;
  y=x; // this yields 1.4, which is cut off

  assert(y==1);

  x=2;
  x -= (__CPROVER_fixedbv[64][32])0.4;
  y=x; // this yields 1.6, which is cut off, too!

  assert(y==1);
}
