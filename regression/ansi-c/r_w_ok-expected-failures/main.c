#include <assert.h>

int main()
{
  int *p = (int *)0;
#ifdef TOO_MANY_ARGS
  assert(!__CPROVER_r_ok(p, sizeof(int), 42));
#elif defined(NOT_A_POINTER)
  assert(!__CPROVER_r_ok(*p, sizeof(int)));
#elif defined(VOID_POINTER_NO_SIZE)
  assert(!__CPROVER_r_ok((void *)p));
#endif
}
