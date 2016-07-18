// deadlock possible

#include "windows.h"

HANDLE m1,m2;

int x;

void thr1(void *arg)
{
  WaitForSingleObject(m1, INFINITE);
  WaitForSingleObject(m2, INFINITE);
  ++x;
  ReleaseMutex(m2);
  ReleaseMutex(m1);
}


void thr2(void *arg)
{
  WaitForSingleObject(m2, INFINITE);
  WaitForSingleObject(m1, INFINITE);
  ++x;
  ReleaseMutex(m1);
  ReleaseMutex(m2);
}


int main()
{
	uintptr_t tHandle [2];

  m1 = CreateMutex (0, FALSE, "m1");       // expect: 1594
  m2 = CreateMutex (0, FALSE, "m2");       // expect: 1594

  tHandle [1] = _beginthread (&thr1, 0, NULL);
  tHandle [2] = _beginthread (&thr2, 0, NULL);

  return 0;
}
