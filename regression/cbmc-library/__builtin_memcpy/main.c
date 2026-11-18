#include <assert.h>
#include <string.h>

// cl does not declare the GCC builtins
#ifndef __GNUC__
void *__builtin_memcpy(void *, const void *, __CPROVER_size_t);
#endif

int main()
{
  int src[] = {1, 2, 3};
  int dst[3];
  __builtin_memcpy(dst, src, sizeof(src));
  assert(dst[0] == 1);
  assert(dst[1] == 2);
  assert(dst[2] == 3);
  return 0;
}
