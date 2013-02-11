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
          
  __CPROVER_HIDE:;
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");
}
