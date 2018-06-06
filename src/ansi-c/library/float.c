/* FUNCTION: _controlfp */

#ifdef _WIN32
#include <float.h>

__CPROVER_thread_local unsigned __CPROVER_fpu_control_word;

unsigned int _controlfp(
  unsigned int new_value,
  unsigned int mask)
{
  __CPROVER_fpu_control_word=
    (__CPROVER_fpu_control_word&~mask)|new_value;

  if((mask&_MCW_RC)!=0)
    __CPROVER_rounding_mode=(new_value&_MCW_RC)>>8;

  return __CPROVER_fpu_control_word;
}

#endif

/* FUNCTION: _status87 */

#ifdef _WIN32

__CPROVER_thread_local unsigned __CPROVER_fpu_control_word;

inline unsigned int _status87(void)
{
  return __CPROVER_fpu_control_word;
}

#endif

/* FUNCTION: _statusfp */

#ifdef _WIN32

__CPROVER_thread_local unsigned __CPROVER_fpu_control_word;

inline unsigned int _statusfp(void)
{
  return __CPROVER_fpu_control_word;
}

#endif

/* FUNCTION: _statusfp2 */

#ifdef _WIN32

__CPROVER_thread_local unsigned __CPROVER_fpu_control_word;

inline void _statusfp2(unsigned int *px86, unsigned int *pSSE2)
{
  unsigned SSE2_status;
  *px86=__CPROVER_fpu_control_word;
  *pSSE2=SSE2_status; // nondet
}

#endif

/* FUNCTION: _isnan */

inline int _isnan(double x)
{
  return __CPROVER_isnand(x);
}

/* FUNCTION: __builtin_flt_rounds */

extern int __CPROVER_rounding_mode;

inline int __builtin_flt_rounds(void)
{
  // This is a clang builtin for FLT_ROUNDS
  // The magic numbers are C99 and different from the
  // x86 encoding that CPROVER uses.
  return __CPROVER_rounding_mode==0?1: // to nearest
         __CPROVER_rounding_mode==1?3: // downward
         __CPROVER_rounding_mode==2?2: // upward
         __CPROVER_rounding_mode==3?0: // to zero
         -1;
}

/* FUNCTION: __flt_rounds */

int __builtin_flt_rounds(void);

inline int __flt_rounds(void)
{
  // Spotted on FreeBSD
  return __builtin_flt_rounds();
}
