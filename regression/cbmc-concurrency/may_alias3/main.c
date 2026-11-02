#include <assert.h>

int *shared_ptr;
_Bool flag;

void thread1(void)
{
  int local = 0;
  shared_ptr = &local;
  flag = 1;
}

int main(void)
{
  int x = 10;
  shared_ptr = &x;
  __CPROVER_ASYNC_1: thread1();
  __CPROVER_assume(flag == 1);
  assert(*shared_ptr == 10);
}
