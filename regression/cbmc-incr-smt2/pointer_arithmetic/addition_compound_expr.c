#include <stdint.h>

#define NULL (void *)0

int main()
{
  int32_t *a;
  __CPROVER_assume(a != NULL);
  int32_t *z = a + 2 * sizeof(int32_t);

  __CPROVER_assert(a != z, "expected successful because of pointer arithmetic");
  __CPROVER_assert(a == z, "expected failure because of pointer arithmetic");
}
