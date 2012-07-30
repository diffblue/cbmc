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
