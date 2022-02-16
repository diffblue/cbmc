#include <assert.h>
#include <limits.h>

#ifdef _MSC_VER
#  include <intrin.h>
#  ifdef _WIN64
#    define _mm_extract_pi16(a, b) _mm_extract_epi16(a, b)
#  endif
#else
#  include <immintrin.h>
#endif

int main()
{
  __m128i values = _mm_setr_epi32(0x1234, 0x2345, 0x3456, 0x4567);
  int val1 = _mm_extract_epi32(values, 0);
  assert(val1 == 0x1234);

#ifndef _WIN64
  __m64 a = _mm_setr_pi16(SHRT_MIN, 10, SHRT_MIN + 1, SHRT_MAX);
  __m64 b = _mm_set_pi16(1, 1, 10, 1);
  __m64 result = _mm_subs_pi16(a, b);
#else
  __m128i a = _mm_setr_epi16(SHRT_MIN, 10, SHRT_MIN + 1, SHRT_MAX, 0, 0, 0, 0);
  __m128i b = _mm_set_epi16(0, 0, 0, 0, 1, 1, 10, 1);
  __m128i result = _mm_subs_epi16(a, b);
#endif
  short s1 = _mm_extract_pi16(result, 0);
  assert(s1 == SHRT_MIN);
  short s2 = _mm_extract_pi16(result, 1);
  assert(s2 == 0);
  short s3 = _mm_extract_pi16(result, 2);
  assert(s3 == SHRT_MIN);
  short s4 = _mm_extract_pi16(result, 3);
  assert(s4 == SHRT_MAX - 1);

#ifndef _WIN64
  result = _mm_adds_pi16(a, b);
#else
  result = _mm_adds_epi16(a, b);
#endif
  s1 = _mm_extract_pi16(result, 0);
  assert(s1 == SHRT_MIN + 1);
  s2 = _mm_extract_pi16(result, 1);
  assert(s2 == 20);
  s3 = _mm_extract_pi16(result, 2);
  assert(s3 == SHRT_MIN + 2);
  s4 = _mm_extract_pi16(result, 3);
  assert(s4 == SHRT_MAX);

  __m128i x = _mm_set_epi16(0, 0, 0, 0, 0, 0, 0, 0);
  __m128i y = _mm_setr_epi16(1, 0, 0, 0, 0, 0, 0, 0);
  __m128i result128 = _mm_subs_epu16(x, y);
  short s = _mm_extract_epi16(result128, 0);
  assert(s == 0);

  return 0;
}
