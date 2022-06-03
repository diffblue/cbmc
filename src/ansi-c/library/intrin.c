/* intrin.h is an include file provided by Visual Studio */

/* FUNCTION: _InterlockedDecrement */

long _InterlockedDecrement(long volatile *p)
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

long _InterlockedExchange(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long old=*p;
  *p=v;
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedExchange16 */

short _InterlockedExchange16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short old=*p;
  *p=v;
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedExchange8 */

char _InterlockedExchange8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char old=*p;
  *p=v;
  __CPROVER_atomic_end();
  return old;
}

/* FUNCTION: _InterlockedExchangeAdd */

long _InterlockedExchangeAdd(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedExchangeAdd16 */

short _InterlockedExchangeAdd16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedExchangeAdd8 */

char _InterlockedExchangeAdd8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedCompareExchange */

long _InterlockedCompareExchange(long volatile *p, long v1, long v2)
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

long long
_InterlockedCompareExchange64(long long volatile *p, long long v1, long long v2)
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

long _InterlockedIncrement(long volatile *p)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=++(*p);
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedOr */

long _InterlockedOr(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)|=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedOr8 */

char _InterlockedOr8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)|=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedOr16 */

short _InterlockedOr16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)|=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedXor */

long _InterlockedXor(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)^=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedXor8 */

char _InterlockedXor8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)^=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedXor16 */

short _InterlockedXor16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)^=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAnd */

long _InterlockedAnd(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)&=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAnd8 */

char _InterlockedAnd8(char volatile *p, char v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  char result=(*p)&=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAnd16 */

short _InterlockedAnd16(short volatile *p, short v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=(*p)&=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAdd */

long _InterlockedAdd(long volatile *p, long v)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  long result=(*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedAddLargeStatistic */

long _InterlockedAddLargeStatistic(long long volatile *p, long v)
{
  __CPROVER_HIDE:;
  // not atomic:
  // http://msdn.microsoft.com/en-us/library/yc92ytxy%28v=vs.90%29.aspx
  (*p)+=v;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  return v;
}

/* FUNCTION: _mm_lfence */

void _mm_lfence(void)
{
  __CPROVER_HIDE:;
}

/* FUNCTION: _mm_mfence */

void _mm_mfence(void)
{
  __CPROVER_HIDE:;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: _WriteBarrier */

void _WriteBarrier(void)
{
  __CPROVER_HIDE:;
}

/* FUNCTION: _ReadWriteBarrier */

void _ReadWriteBarrier(void)
{
  __CPROVER_HIDE:;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: _ReadBarrier */

void _ReadBarrier(void)
{
  __CPROVER_HIDE:;
}

/* FUNCTION: _InterlockedIncrement16 */

short _InterlockedIncrement16(short volatile *p)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=++(*p);
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedDecrement16 */

short _InterlockedDecrement16(short volatile *p)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  short result=--(*p);
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: _InterlockedCompareExchange16 */

short _InterlockedCompareExchange16(short volatile *p, short v1, short v2)
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

char _InterlockedCompareExchange8(char volatile *p, char v1, char v2)
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

__m128i _mm_set_epi32(int e3, int e2, int e1, int e0)
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

__m128i _mm_setr_epi32(int e3, int e2, int e1, int e0)
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

__m128i _mm_set_epi16(
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

__m128i _mm_setr_epi16(
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

__m64 _mm_set_pi16(short e3, short e2, short e1, short e0)
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

__m64 _mm_setr_pi16(short e3, short e2, short e1, short e0)
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

int _mm_extract_epi32(__m128i a, const int imm8)
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

int _mm_extract_epi16(__m128i a, const int imm8)
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

int _mm_extract_pi16(__m64 a, const int imm8)
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

__m128i _mm_adds_epi16(__m128i a, __m128i b)
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

__m128i _mm_subs_epi16(__m128i a, __m128i b)
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

/* FUNCTION: _mm_adds_epu16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

__m128i _mm_adds_epu16(__m128i a, __m128i b)
{
  return (__m128i){
    .m128i_i16 = {
      __CPROVER_saturating_plus(a.m128i_u16[0], b.m128i_u16[0]),
      __CPROVER_saturating_plus(a.m128i_u16[1], b.m128i_u16[1]),
      __CPROVER_saturating_plus(a.m128i_u16[2], b.m128i_u16[2]),
      __CPROVER_saturating_plus(a.m128i_u16[3], b.m128i_u16[3]),
      __CPROVER_saturating_plus(a.m128i_u16[4], b.m128i_u16[4]),
      __CPROVER_saturating_plus(a.m128i_u16[5], b.m128i_u16[5]),
      __CPROVER_saturating_plus(a.m128i_u16[6], b.m128i_u16[6]),
      __CPROVER_saturating_plus(a.m128i_u16[7], b.m128i_u16[7]),
    }};
}
#endif

/* FUNCTION: _mm_subs_epu16 */

#ifdef _MSC_VER
#  ifndef __CPROVER_INTRIN_H_INCLUDED
#    include <intrin.h>
#    define __CPROVER_INTRIN_H_INCLUDED
#  endif

__m128i _mm_subs_epu16(__m128i a, __m128i b)
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
