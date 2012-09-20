#ifdef __MMX__
#include "emmintrin.h"
#endif

int main()
{
  int  nonsense1;
#ifdef __MMX__
  __m128i qq = {0};
#endif
  return (0);
}
