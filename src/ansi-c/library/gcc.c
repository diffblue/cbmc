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
