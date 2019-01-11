#include <assert.h>

enum E
{
  A = 1,
  B = 16
};

int main()
{
  enum E e = A;
  e <<= 4;
  assert(e == B);
  e >>= 4;
  assert(e == A);
  e |= B;
  e ^= A;
  assert(e == B);
  e -= 15;
  assert(e == A);
  return 0;
}
