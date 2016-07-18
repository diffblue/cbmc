// deadlock possible

#include "windows.h"

HANDLE m1,m2;       // expect: 1594,1594

int x;

DWORD thr1(void *arg)        // expect: 1568
{
  WaitForSingleObject(m1, INFINITE);
  WaitForSingleObject(m2, INFINITE);
  ++x;
  ReleaseMutex(m2);
  ReleaseMutex(m1);

  int k=0;

  return 0;
}


DWORD thr2(void *arg)        // expect: 1568
{
  WaitForSingleObject(m2, INFINITE);
  WaitForSingleObject(m1, INFINITE);
  ++x;
  ReleaseMutex(m1);
  ReleaseMutex(m2);

  return 0;
}


int main()
{
  HANDLE tHandle [2];

  m1 = CreateMutex (0, FALSE, "m1");
  m2 = CreateMutex (0, FALSE, "m2");

  tHandle [1] = CreateThread (0, 0, &thr1, 0, 0, 0);
  tHandle [2] = CreateThread (0, 0, &thr2, 0, 0, 0);

  WaitForMultipleObjects (2, tHandle, TRUE, INFINITE);

  return 0;
}
