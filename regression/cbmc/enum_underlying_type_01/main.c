#include <assert.h>

enum enum1
{
  E1
};

enum enum2 : signed char
{
  E2
};

typedef signed char signed_char_t;

enum enum3 : signed_char_t
{
  E3
};

int main()
{
  assert(sizeof(int) != sizeof(signed char));
  assert(sizeof(enum enum1) == sizeof(int));
  assert(sizeof(enum enum2) == sizeof(signed char));
  assert(sizeof(enum enum3) == sizeof(signed char));

  enum enum2 e2 = 0xff;
  assert(e2 == -1);

  enum enum3 e3 = 0xff;
  assert(e3 == -1);
}
