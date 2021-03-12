#include <assert.h>
#ifdef _MSC_VER
#  include <intrin.h>
#else
#  include <immintrin.h>
#endif

int main()
{
  __m128i values = _mm_setr_epi32(0x1234, 0x2345, 0x3456, 0x4567);
  int val1 = _mm_extract_epi32(values, 0);
  assert(val1 == 0x1234);
  return 0;
}
