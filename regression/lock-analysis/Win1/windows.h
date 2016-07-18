#ifndef PRQA_WINDOWS_H
#define PRQA_WINDOWS_H

#define WINAPI
#define _In_
#define _In_opt_
#define _Out_opt_

#define TRUE 1
#define FALSE 0

typedef int BOOL;
typedef unsigned long DWORD;
typedef void *LPVOID;
typedef void *PVOID;
typedef const char *LPCSTR;
typedef LPCSTR LPCTSTR;
typedef PVOID HANDLE;
typedef DWORD (WINAPI *LPTHREAD_START_ROUTINE) (
    _In_ LPVOID lpThreadParameter
);
typedef struct _SECURITY_ATTRIBUTES {
  DWORD  nLength;
  LPVOID lpSecurityDescriptor;
  BOOL   bInheritHandle;
} SECURITY_ATTRIBUTES, *PSECURITY_ATTRIBUTES, *LPSECURITY_ATTRIBUTES;

HANDLE CreateThread(
  LPSECURITY_ATTRIBUTES lpsa,
  DWORD dwStackSize,
  LPTHREAD_START_ROUTINE pfnThreadProc,
  void* pvParam,
  DWORD dwCreationFlags,
  DWORD* pdwThreadId 
);

DWORD WINAPI WaitForSingleObject(
  _In_ HANDLE hHandle,
  _In_ DWORD  dwMilliseconds
);

DWORD WINAPI WaitForMultipleObjects(
  _In_       DWORD  nCount,
  _In_ const HANDLE *lpHandles,
  _In_       BOOL   bWaitAll,
  _In_       DWORD  dwMilliseconds
);

//we have to guarantee that CreateMutex returns a pointer to a valid object
#if 1
//the macro implementation guarantees soundness 
#define CreateMutex(lpMutexAttributes,bInitialOwner,lpName) \
  (HANDLE)malloc(sizeof(DWORD))
#else
HANDLE WINAPI CreateMutex(
  _In_opt_ LPSECURITY_ATTRIBUTES lpMutexAttributes,
  _In_     BOOL                  bInitialOwner,
  _In_opt_ LPCTSTR               lpName
)
{
  return (HANDLE)malloc(sizeof(DWORD));
}
#endif

BOOL WINAPI ReleaseMutex(
  _In_ HANDLE hMutex
);

typedef unsigned int uintptr_t;

typedef void     (WINAPI* _beginthread_proc_type)(void*);
typedef unsigned (WINAPI* _beginthreadex_proc_type)(void*);

uintptr_t WINAPI _beginthread(
    _In_     _beginthread_proc_type _StartAddress,
    _In_     unsigned               _StackSize,
    _In_opt_ void*                  _ArgList
    );

void WINAPI _endthread(void);

uintptr_t WINAPI _beginthreadex(
    _In_opt_  void*                    _Security,
    _In_      unsigned                 _StackSize,
    _In_      _beginthreadex_proc_type _StartAddress,
    _In_opt_  void*                    _ArgList,
    _In_      unsigned                 _InitFlag,
    _Out_opt_ unsigned*                _ThrdAddr
    );

void WINAPI _endthreadex(
    _In_ unsigned _ReturnCode
    );

#define INFINITE 0

#ifndef NULL
#define NULL 0
#endif

#endif
