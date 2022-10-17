#include <stdlib.h>

int main()
{
  size_t s;
  char *p = malloc(s);
  // at __CPROVER_max_malloc_size p + s would overflow; all larger values of s
  // make malloc return NULL when using --malloc-fail-null
  if(p != NULL && s != __CPROVER_max_malloc_size)
  {
    char *q = p + s;
    __CPROVER_assert(__CPROVER_r_ok(q, 0), "should be valid");
    __CPROVER_assert(!__CPROVER_r_ok(q + 1, 0), "should fail");
  }
}
