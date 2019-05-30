/* FUNCTION: __builtin_ia32_sfence */

inline void __builtin_ia32_sfence(void)
{
  __asm("sfence");
}

/* FUNCTION: __builtin_ia32_lfence */

inline void __builtin_ia32_lfence(void)
{
  __asm("lfence");
}

/* FUNCTION: __builtin_ia32_mfence */

inline void __builtin_ia32_mfence(void)
{
  __asm("mfence");
}

/* FUNCTION: __sync_synchronize */

inline void __sync_synchronize(void)
{
  // WARNING: this was a NOP before gcc 4.3.1,
  // but is now believed to be the strongest possible barrier.

  #if (__GNUC__ * 10000 + __GNUC_MINOR__ * 100 + __GNUC_PATCHLEVEL__) >= 40301
  __CPROVER_HIDE:;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");
  #endif
}

/* FUNCTION: __builtin_clz */

int __builtin_popcount(unsigned int);

inline int __builtin_clz(unsigned int x)
{
  __CPROVER_precondition(x != 0, "__builtin_clz(0) is undefined");

  x = x | (x >> 1);
  x = x | (x >> 2);
  x = x | (x >> 4);
  x = x | (x >> 8);
  if(sizeof(x) >= 4)
    x = x | (x >> 16);

  return __builtin_popcount(~x);
}

/* FUNCTION: __builtin_clzl */

int __builtin_popcountl(unsigned long int);

inline int __builtin_clzl(unsigned long int x)
{
  __CPROVER_precondition(x != 0, "__builtin_clzl(0) is undefined");

  x = x | (x >> 1);
  x = x | (x >> 2);
  x = x | (x >> 4);
  x = x | (x >> 8);
  if(sizeof(x) >= 4)
    x = x | (x >> 16);
  if(sizeof(x) >= 8)
    x = x | (x >> 32);

  return __builtin_popcountl(~x);
}

/* FUNCTION: __builtin_clzll */

int __builtin_popcountll(unsigned long long int);

inline int __builtin_clzll(unsigned long long int x)
{
  __CPROVER_precondition(x != 0, "__builtin_clzll(0) is undefined");

  x = x | (x >> 1);
  x = x | (x >> 2);
  x = x | (x >> 4);
  x = x | (x >> 8);
  if(sizeof(x) >= 4)
    x = x | (x >> 16);
  if(sizeof(x) >= 8)
    x = x | (x >> 32);

  return __builtin_popcountll(~x);
}

/* FUNCTION: __atomic_test_and_set */

void __atomic_thread_fence(int memorder);

inline _Bool __atomic_test_and_set(void *ptr, int memorder)
{
__CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  _Bool result = *(char *)ptr == 1;
  *(char *)ptr = 1;
  __atomic_thread_fence(memorder);
  __CPROVER_atomic_end();
  return result;
}

/* FUNCTION: __atomic_clear */

void __atomic_thread_fence(int memorder);

inline void __atomic_clear(_Bool *ptr, int memorder)
{
__CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  *(char *)ptr = 0;
  __atomic_thread_fence(memorder);
  __CPROVER_atomic_end();
}

/* FUNCTION: __atomic_thread_fence */

#if __STDC_VERSION__ >= 201112L
// GCC 4.8 did claim to support C++11, but failed to ship stdatomic.h
#  if !defined(__GNUC__) || (__GNUC__ * 100 + __GNUC_MINOR__) >= 409
#    include <stdatomic.h>
#  endif
#endif

#ifndef __ATOMIC_RELAXED
#  define __ATOMIC_RELAXED 0
#endif

#ifndef __ATOMIC_CONSUME
#  define __ATOMIC_CONSUME 1
#endif

#ifndef __ATOMIC_ACQUIRE
#  define __ATOMIC_ACQUIRE 2
#endif

#ifndef __ATOMIC_RELEASE
#  define __ATOMIC_RELEASE 3
#endif

#ifndef __ATOMIC_ACQ_REL
#  define __ATOMIC_ACQ_REL 4
#endif

#ifndef __ATOMIC_SEQ_CST
#  define __ATOMIC_SEQ_CST 5
#endif

inline void __atomic_thread_fence(int memorder)
{
__CPROVER_HIDE:;
  if(memorder == __ATOMIC_CONSUME || memorder == __ATOMIC_ACQUIRE)
    __CPROVER_fence("RRfence", "RWfence", "RRcumul", "RWcumul");
  else if(memorder == __ATOMIC_RELEASE)
    __CPROVER_fence("WRfence", "WWfence", "WRcumul", "WWcumul");
  else if(memorder == __ATOMIC_ACQ_REL || memorder == __ATOMIC_SEQ_CST)
    __CPROVER_fence(
      "WWfence",
      "RRfence",
      "RWfence",
      "WRfence",
      "WWcumul",
      "RRcumul",
      "RWcumul",
      "WRcumul");
}

/* FUNCTION: __atomic_signal_fence */

void __atomic_thread_fence(int memorder);

inline void __atomic_signal_fence(int memorder)
{
__CPROVER_HIDE:;
  __atomic_thread_fence(memorder);
}

/* FUNCTION: __atomic_always_lock_free */

inline _Bool __atomic_always_lock_free(__CPROVER_size_t size, void *ptr)
{
__CPROVER_HIDE:;
  (void)ptr;
  return size <= sizeof(__CPROVER_size_t);
}

/* FUNCTION: __atomic_is_lock_free */

inline _Bool __atomic_is_lock_free(__CPROVER_size_t size, void *ptr)
{
__CPROVER_HIDE:;
  (void)ptr;
  return size <= sizeof(__CPROVER_size_t);
}
