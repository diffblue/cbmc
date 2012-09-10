#include <assert.h>
#include <stdio.h>

int main()
{
  #ifdef __GNUC__
  _Complex c;
  c=1.0i+2;

  assert(__real__ c == 2);
  assert(__imag__ c == 1);  
  
  _Complex double d;
  assert(sizeof(c)==sizeof(d));
  
  _Complex char char_complex, char_complex2;
  
  char_complex=0x3i-2;
  
  assert(sizeof(d)==sizeof(c));
  assert(sizeof(char_complex)==sizeof(char)*2);

  // the real part is stored first in memory  
  assert(((char *)&char_complex)[0]==-2);
  assert(((char *)&char_complex)[1]==3);

  assert(__real__ char_complex == -2);
  assert(__imag__ char_complex == 3);
  
  // complex conjugate
  char_complex2 = ~ char_complex;
  #else
  
  // Visual studio doesn't have it  

  #endif
}
