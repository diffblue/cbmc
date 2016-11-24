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

