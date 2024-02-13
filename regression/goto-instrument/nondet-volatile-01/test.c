#include <assert.h>

enum E
{
  A,
  B
};

void main()
{
  int a[2] = {0};

  volatile int i = 0;
  a[i] = 1;

  assert(a[1] == 0); // should fail

  // make sure the use of enum (tags) does not cause infinite recursion
  enum A e = A;
  e = e;
}
