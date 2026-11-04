#include <assert.h>

int main(void)
{
  // signed char - unsigned char -> unsigned int:
  // -64 - 128 = -192 does not fit in unsigned int.
  {
    signed char a = -64;
    unsigned char b = 128;
    unsigned int r;
    assert(__builtin_sub_overflow(a, b, &r));
  }

  // signed char * unsigned char -> signed char:
  // 25 * 251 = 6275 does not fit in signed char.
  {
    signed char c = 25;
    unsigned char d = 251;
    signed char s;
    assert(__builtin_mul_overflow(c, d, &s));
  }

  // signed char + unsigned char -> signed char:
  // 1 + 200 = 201 does not fit in signed char.
  {
    signed char a = 1;
    unsigned char b = 200;
    signed char r;
    assert(__builtin_add_overflow(a, b, &r));
  }

  // Same-type: no overflow, result correct.
  {
    signed char a = 1;
    unsigned char b = 2;
    unsigned char r;
    assert(!__builtin_add_overflow(a, b, &r));
    assert(r == 3);
  }

  // _p variant: signed char + unsigned char -> signed char.
  {
    signed char a = 1;
    unsigned char b = 200;
    assert(__builtin_add_overflow_p(a, b, (signed char)0));
  }

  return 0;
}
