#include <assert.h>

int start_main = 0;
int mStartLock = 0;
int __COUNT__ = 0;

void __VERIFIER_atomic_acquire()
{
  __CPROVER_assume(mStartLock == 0);
  mStartLock = 1;
}

void __VERIFIER_atomic_release()
{
  __CPROVER_assume(mStartLock == 1);
  mStartLock = 0;
}

void __VERIFIER_atomic_thr1()
{
  if(__COUNT__ == 0)
  {
    __COUNT__ = __COUNT__ + 1;
  }
  else
  {
    assert(0);
  }
}

void thr1()
{
  __VERIFIER_atomic_acquire();
  start_main = 1;
  __VERIFIER_atomic_thr1();
  __VERIFIER_atomic_release();
}

void __VERIFIER_atomic_thr2()
{
  if(__COUNT__ == 1)
  {
    __COUNT__ = __COUNT__ + 1;
  }
  else
  {
    assert(0);
  }
}

void thr2()
{
  __CPROVER_assume(start_main != 0);
  __VERIFIER_atomic_acquire();
  __VERIFIER_atomic_release();
  __VERIFIER_atomic_thr2();
}

int main()
{
__CPROVER_ASYNC_1:
  thr1();

  thr2();

  return 0;
}
