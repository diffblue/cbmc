#include <assert.h>

int main()
{
  #ifdef __GNUC__
  _Complex c; // this is usually '_Complex double'
  c=1.0i+2;

  assert(__real__ c == 2);
  assert(__imag__ c == 1);

  _Complex double d;
  assert(sizeof(c)==sizeof(d));

  _Complex signed char char_complex, char_complex2;

  char_complex=0x3i-2;

  assert(sizeof(d)==sizeof(c));
  assert(sizeof(char_complex)==sizeof(signed char)*2);

  // The real part is stored first in memory on i386.
  // Need to find out about other architectures.
  #if defined(__i386__) || defined(__amd64__)
  assert(((signed char *)&char_complex)[0]==-2);
  assert(((signed char *)&char_complex)[1]==3);
  #endif

  assert(__real__ char_complex == -2);
  assert(__imag__ char_complex == 3);

  // the precedence of __imag__ is higher than that of +
  assert((__imag__ 1.0i + 1.0i) == 1.0i + 1.0);

  // complex conjugate
  char_complex2 = ~ char_complex;

  // __real__ something is an lvalue!
  __real__ char_complex = 100;
  assert(__real__ char_complex == 100);
  assert(__imag__ char_complex == 3);

  // can be incremented
  char_complex++;
  assert(__real__ char_complex == 101);
  assert(__imag__ char_complex == 3);

  // also separately
  (__real__ char_complex)++;
  assert(__real__ char_complex == 102);
  assert(__imag__ char_complex == 3);

  // casts to reals produce the real part
  assert((int) char_complex == 102);

  #else

  // Visual studio doesn't have it

  #endif
}
