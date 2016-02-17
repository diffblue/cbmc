#ifdef __MMX__
#include "mmintrin.h"
#endif

int main()
{
  __m64 x;
  
  long long unsigned di;
  
  x=(__m64)di;  

  return 0;
}
