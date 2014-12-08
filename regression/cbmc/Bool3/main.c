#include <assert.h>

int main() {
  _Bool b1;

  // _NOT_ guaranteed to be 0 or 1
  assert(b1==0 || b1==1);
}
