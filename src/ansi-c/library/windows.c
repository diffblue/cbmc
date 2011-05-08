/* FUNCTION: QueryPerformanceFrequency */

#include <windows.h>

BOOL QueryPerformanceFrequency(LARGE_INTEGER *lpFrequency)
{
  __CPROVER_HIDE:;
  __int64 result;
  lpFrequency->QuadPart=result;
  _Bool error;
  if(error) return 0;
  __CPROVER_assume(result!=0);
  return 1;
}

          