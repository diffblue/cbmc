#ifdef __MMX__
#include "emmintrin.h"
#endif

int main()
{
  int  nonsense1;
#ifdef __MMX__
  __m128i qq = {0};
  __m128 f = {1.0f, 1.0f, 1.0f, 1.0f};
#endif
  return (0);
}
