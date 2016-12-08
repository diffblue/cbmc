#include <pthread.h>

_Thread_local _Bool l1;
_Thread_local _Bool l2=1;

void* thr1(void* arg)
{
	__CPROVER_assert(!l1, "");
	l1 = 1;
	__CPROVER_assert(l2, "");

  return 0;
}

int main()
{
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  pthread_create(&t, 0, thr1, 0);
}
