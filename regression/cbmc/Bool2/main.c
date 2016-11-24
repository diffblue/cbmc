#include <assert.h>

_Bool nondet_bool();

int main() {
  _Bool b1=nondet_bool();

  // guaranteed to be 0 or 1
  assert(b1==0 || b1==1);
}
