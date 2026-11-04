#include <assert.h>
#include <stdint.h>

int main()
{
  char x;
  char *p = &x;
  uint64_t k;

  char *r = p + k;

  // The propositional encoding used to wrap pointer offsets at
  // 2^(pointer_width - object_bits), making r alias p for k a non-zero
  // multiple of that value, while the simplifier and constant propagation
  // compute pointer arithmetic in full-width arithmetic. Both must agree
  // that adding a non-zero k (modulo the full address width) yields a
  // different pointer.
  if(k == (1ULL << 48))
    assert(r != p);

  if(k != 0)
    assert(r != p);

  // Constant-offset variant (folded by constant propagation).
  char *q = p + (1ULL << 48);
  assert(q != p);

  return 0;
}
