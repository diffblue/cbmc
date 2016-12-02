#ifdef __MMX__
#include "mmintrin.h"
#endif

int main()
{
  // This is a gcc extension
  #ifdef __GNUC__
  #ifdef __MMX__
  __m64 x;

  long long unsigned di;

  x=(__m64)di;
  #endif
  #endif

  return 0;
}
