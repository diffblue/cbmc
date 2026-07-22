#include <assert.h>
#include <stddef.h>

// Must match --object-bits in test.desc.
#define OBJECT_BITS 16

int main()
{
  char x;
  char *p = &x;
  size_t k;

  char *r = p + k;

  // The smallest offset that does not fit the offset field of the pointer
  // encoding.
  const size_t wrap = (size_t)1 << (sizeof(char *) * 8 - OBJECT_BITS);

  // The pointer encoding used to wrap pointer offsets at `wrap`, making r
  // alias p for k a non-zero multiple of that value, while the simplifier and
  // constant propagation compute pointer arithmetic in full-width arithmetic.
  // Both must agree that adding a non-zero k (modulo the full address width)
  // yields a different pointer.
  if(k == wrap)
    assert(r != p);

  if(k != 0)
    assert(r != p);

  // Constant-offset variant (folded by constant propagation).
  char *q = p + wrap;
  assert(q != p);

  return 0;
}
