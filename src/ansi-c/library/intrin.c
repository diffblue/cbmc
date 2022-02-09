/* intrin.h is an include file provided by Visual Studio */

/* FUNCTION: _InterlockedDecrement */

inline long _InterlockedDecrement(long volatile *p)
{
  __CPROVER_HIDE:;
  // This function generates a full memory barrier (or fence) to ensure that
  // memory operations are completed in order.
  __CPROVER_atomic_begin();
  long result=--(*p);
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedExchange */

inline long _InterlockedExchange(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long old=*p;
  *p=v;
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedExchange16 */

inline short _InterlockedExchange16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short old=*p;
  *p=v;
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedExchange8 */

inline char _InterlockedExchange8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char old=*p;
  *p=v;
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedExchangeAdd */

inline long _InterlockedExchangeAdd(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedExchangeAdd16 */

inline short _InterlockedExchangeAdd16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedExchangeAdd8 */

inline char _InterlockedExchangeAdd8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedCompareExchange */

inline long _InterlockedCompareExchange(long volatile *p, long v1, long v2)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long old=(*p);
  *p=(old==v2)?v1:old;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedCompareExchange64 */

inline long long _InterlockedCompareExchange64(long long volatile *p, long long v1, long long v2)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long long old=(*p);
  *p=(old==v2)?v1:old;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: __InterlockedIncrement */

inline long _InterlockedIncrement(long volatile *p)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=++(*p);
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedOr */

inline long _InterlockedOr(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)|=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedOr8 */

inline char _InterlockedOr8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)|=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedOr16 */

inline short _InterlockedOr16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)|=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedXor */

inline long _InterlockedXor(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)^=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedXor8 */

inline char _InterlockedXor8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)^=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedXor16 */

inline short _InterlockedXor16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)^=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAnd */

inline long _InterlockedAnd(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)&=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAnd8 */

inline char _InterlockedAnd8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)&=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAnd16 */

inline short _InterlockedAnd16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)&=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAdd */

inline long _InterlockedAdd(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAddLargeStatistic */

inline long _InterlockedAddLargeStatistic(long long volatile *p, long v)
{
  __CPROVER_HIDE:;
  // not atomic:
  // http://msdn.microsoft.com/en-us/library/yc92ytxy%28v=vs.90%29.aspx
  (*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  return v;
}

/* FUNCTION: _mm_lfence */

inline void _mm_lfence(void)
{
  __CPROVER_HIDE:;
}

/* FUNCTION: _mm_mfence */

inline void _mm_mfence(void)
{
  __CPROVER_HIDE:;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: _WriteBarrier */

inline void _WriteBarrier(void)
{
  __CPROVER_HIDE:;
}

/* FUNCTION: _ReadWriteBarrier */

inline void _ReadWriteBarrier(void)
{
  __CPROVER_HIDE:;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: _ReadBarrier */

inline void _ReadBarrier(void)
{
  __CPROVER_HIDE:;
}

/* FUNCTION: _InterlockedIncrement16 */

inline short _InterlockedIncrement16(short volatile *p)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=++(*p);
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedDecrement16 */

inline short _InterlockedDecrement16(short volatile *p)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=--(*p);
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedCompareExchange16 */

inline short _InterlockedCompareExchange16(short volatile *p, short v1, short v2)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short old=(*p);
  *p=(old==v2)?v1:old;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedCompareExchange8 */

inline char _InterlockedCompareExchange8(char volatile *p, char v1, char v2)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char old=(*p);
  *p=(old==v2)?v1:old;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _mm_set_epi32 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_set_epi32(int e3, int e2, int e1, int e0)
{
  return (__m128i){.m128i_i32 = {e0, e1, e2, e3}};
}
#endif

/* FUNCTION: _mm_setr_epi32 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_setr_epi32(int e3, int e2, int e1, int e0)
{
  return (__m128i){.m128i_i32 = {e3, e2, e1, e0}};
}
#endif

/* FUNCTION: _mm_set_epi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_set_epi16(
  short e7,
  short e6,
  short e5,
  short e4,
  short e3,
  short e2,
  short e1,
  short e0)
{
  return (__m128i){.m128i_i16 = {e0, e1, e2, e3, e4, e5, e6, e7}};
}
#endif

/* FUNCTION: _mm_setr_epi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_setr_epi16(
  short e7,
  short e6,
  short e5,
  short e4,
  short e3,
  short e2,
  short e1,
  short e0)
{
  return (__m128i){.m128i_i16 = {e7, e6, e5, e4, e3, e2, e1, e0}};
}
#endif

/* FUNCTION: _mm_set_pi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m64 _mm_set_pi16(short e3, short e2, short e1, short e0)
{
  return (__m64){.m64_i16 = {e0, e1, e2, e3}};
}
#endif

/* FUNCTION: _mm_setr_pi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m64 _mm_setr_pi16(short e3, short e2, short e1, short e0)
{
  return (__m64){.m64_i16 = {e3, e2, e1, e0}};
}
#endif

/* FUNCTION: _mm_extract_epi32 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline int _mm_extract_epi32(__m128i a, const int imm8)
{
  return a.m128i_i32[imm8];
}
#endif

/* FUNCTION: _mm_extract_epi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline int _mm_extract_epi16(__m128i a, const int imm8)
{
  return a.m128i_i16[imm8];
}
#endif

/* FUNCTION: _mm_extract_pi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline int _mm_extract_pi16(__m64 a, const int imm8)
{
  return a.m64_i16[imm8];
}
#endif

/* FUNCTION: _mm_adds_epi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_adds_epi16(__m128i a, __m128i b)
{
  return (__m128i){
    .m128i_i16 = {
      __CPROVER_saturating_plus(a.m128i_i16[0], b.m128i_i16[0]),
      __CPROVER_saturating_plus(a.m128i_i16[1], b.m128i_i16[1]),
      __CPROVER_saturating_plus(a.m128i_i16[2], b.m128i_i16[2]),
      __CPROVER_saturating_plus(a.m128i_i16[3], b.m128i_i16[3]),
      __CPROVER_saturating_plus(a.m128i_i16[4], b.m128i_i16[4]),
      __CPROVER_saturating_plus(a.m128i_i16[5], b.m128i_i16[5]),
      __CPROVER_saturating_plus(a.m128i_i16[6], b.m128i_i16[6]),
      __CPROVER_saturating_plus(a.m128i_i16[7], b.m128i_i16[7]),
    }};
}
#endif

/* FUNCTION: _mm_subs_epi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_subs_epi16(__m128i a, __m128i b)
{
  return (__m128i){
    .m128i_i16 = {
      __CPROVER_saturating_minus(a.m128i_i16[0], b.m128i_i16[0]),
      __CPROVER_saturating_minus(a.m128i_i16[1], b.m128i_i16[1]),
      __CPROVER_saturating_minus(a.m128i_i16[2], b.m128i_i16[2]),
      __CPROVER_saturating_minus(a.m128i_i16[3], b.m128i_i16[3]),
      __CPROVER_saturating_minus(a.m128i_i16[4], b.m128i_i16[4]),
      __CPROVER_saturating_minus(a.m128i_i16[5], b.m128i_i16[5]),
      __CPROVER_saturating_minus(a.m128i_i16[6], b.m128i_i16[6]),
      __CPROVER_saturating_minus(a.m128i_i16[7], b.m128i_i16[7]),
    }};
}
#endif

/* FUNCTION: _mm_subs_epi16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_subs_epi16(__m128i a, __m128i b)
{
  return (__m128i){
    .m128i_i16 = {
      __CPROVER_saturating_minus(a.m128i_i16[0], b.m128i_i16[0]),
      __CPROVER_saturating_minus(a.m128i_i16[1], b.m128i_i16[1]),
      __CPROVER_saturating_minus(a.m128i_i16[2], b.m128i_i16[2]),
      __CPROVER_saturating_minus(a.m128i_i16[3], b.m128i_i16[3]),
      __CPROVER_saturating_minus(a.m128i_i16[4], b.m128i_i16[4]),
      __CPROVER_saturating_minus(a.m128i_i16[5], b.m128i_i16[5]),
      __CPROVER_saturating_minus(a.m128i_i16[6], b.m128i_i16[6]),
      __CPROVER_saturating_minus(a.m128i_i16[7], b.m128i_i16[7]),
    }};
}
#endif

/* FUNCTION: _mm_subs_epu16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

inline __m128i _mm_subs_epu16(__m128i a, __m128i b)
{
  return (__m128i){
    .m128i_u16 = {
      __CPROVER_saturating_minus(a.m128i_u16[0], b.m128i_u16[0]),
      __CPROVER_saturating_minus(a.m128i_u16[1], b.m128i_u16[1]),
      __CPROVER_saturating_minus(a.m128i_u16[2], b.m128i_u16[2]),
      __CPROVER_saturating_minus(a.m128i_u16[3], b.m128i_u16[3]),
      __CPROVER_saturating_minus(a.m128i_u16[4], b.m128i_u16[4]),
      __CPROVER_saturating_minus(a.m128i_u16[5], b.m128i_u16[5]),
      __CPROVER_saturating_minus(a.m128i_u16[6], b.m128i_u16[6]),
      __CPROVER_saturating_minus(a.m128i_u16[7], b.m128i_u16[7]),
    }};
}
#endif
