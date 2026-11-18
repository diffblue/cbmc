#include <assert.h>
#include <stdlib.h>

// cl does not declare the GCC builtins
#ifndef __GNUC__
void *__builtin_memcpy(void *, const void *, __CPROVER_size_t);
void *__builtin_memmove(void *, const void *, __CPROVER_size_t);
#endif

// The compiler builtins accept a null pointer when the length is zero -- the
// shape of libc++'s vector relocation on an empty vector
// (`__builtin_memcpy(new_begin, old_begin /* nullptr */, 0)').  C2y (N3322)
// makes zero-length operations on null pointers well-defined; the library
// function memcpy keeps C17's stricter precondition.
int main()
{
  int *dst = malloc(4 * sizeof(int));
  int *src = NULL;
  __builtin_memcpy(dst, src, 0);
  __builtin_memmove(dst, src, 0);
  __builtin_memcpy(src, dst, 0);
  __builtin_memmove(src, dst, 0);
  // copying an empty vector into an empty one
  __builtin_memcpy(src, src, 0);
  __builtin_memmove(src, src, 0);
  int a[2] = {1, 2}, b[2] = {0, 0};
  __builtin_memcpy(b, a, sizeof(a));
  assert(b[0] == 1 && b[1] == 2);
  free(dst);
  return 0;
}
