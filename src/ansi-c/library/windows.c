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

/* FUNCTION: ExitThread */

#include <windows.h>

VOID ExitThread(DWORD dwExitCode)
{
  // never returns
  __CPROVER_assume(0);
}

/* FUNCTION: CreateThread */

#include <windows.h>

HANDLE CreateThread(
  LPSECURITY_ATTRIBUTES lpThreadAttributes,
  SIZE_T dwStackSize,
  LPTHREAD_START_ROUTINE lpStartAddress,
  LPVOID lpParameter,
  DWORD dwCreationFlags,
  LPDWORD lpThreadId
)
{
  __CPROVER_HIDE:;
  DWORD thread_id;

  if(lpThreadId) *lpThreadId=thread_id;
  __CPROVER_ASYNC_1: lpStartAddress(lpParameter);
  
  HANDLE handle;
  return handle;
}
