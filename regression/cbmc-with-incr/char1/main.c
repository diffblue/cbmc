#include <assert.h>

int main()
{
  #ifdef _MSC_VER
  #ifndef _CHAR_UNSIGNED
  #error _CHAR_UNSIGNED should be set
  #endif
  #endif
  
  #ifdef __GNUC__
  #ifndef __CHAR_UNSIGNED__
  #error __CHAR_UNSIGNED__ should be set
  #endif
  #endif

  assert(((char)200)==200);
  assert(((char)-1)==255);

  assert(((signed char)200)==-56);
  assert(((signed char)-1)==-1);
}
