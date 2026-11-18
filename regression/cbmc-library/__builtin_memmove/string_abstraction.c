#include <assert.h>
#include <string.h>

// cl does not declare the GCC builtins
#ifndef __GNUC__
void *__builtin_memmove(void *, const void *, __CPROVER_size_t);
#endif

int main()
{
  char src[4] = "x";
  char dst[4] = "yyy";
  __builtin_memmove(dst, src, 2);
  assert(strlen(dst) == 1);
  // not known to be zero-terminated before the copy
  char dst2[4];
  __builtin_memmove(dst2, src, 2);
  assert(strlen(dst2) == 1);
  return 0;
}
