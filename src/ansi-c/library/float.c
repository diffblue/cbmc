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
