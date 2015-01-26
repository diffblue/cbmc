#include <assert.h>

int main() {
  _Bool b1, b2;

  b1=1;
  b1 ^= (_Bool)1;
  assert(!b1);
  
  b1=1;
  b2=1;
  b1 ^= b2;
  assert(!b1);

  b1=1;
  b1 ^= (1==1);
  assert(!b1);

  b1=1;
  b1 ^= 2;
  assert(b1);

  b1=1;
  b1 ^= 3;
  assert(b1);

  b1=1;
  b1 &= 2;
  assert(!b1);

  b1=0;
  b1 ^= 2;
  assert(b1==1);
}
