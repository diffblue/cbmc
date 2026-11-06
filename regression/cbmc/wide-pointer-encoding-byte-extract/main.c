#include <stddef.h>

// Exercises the wide pointer encoding's byte_extract handling for a source
// that is an array of pointers (bv_pointerst::convert_byte_extract): a pointer
// is read back out of the array via a byte offset, hitting both the
// constant-offset slice and the symbolic-offset multiplexer.

int *parr[4];
int x;
size_t nondet_size_t(void);

void main()
{
  parr[2] = &x;
  parr[3] = &x;

  // Constant byte offset: hits the constant-offset slice.
  int *pc = *(int **)((char *)parr + 2 * sizeof(int *));
  __CPROVER_assert(pc == &x, "constant-offset pointer-array byte_extract");

  // Symbolic byte offset: hits the offset multiplexer.
  size_t off = nondet_size_t();
  __CPROVER_assume(off == 3 * sizeof(int *));
  int *ps = *(int **)((char *)parr + off);
  __CPROVER_assert(ps == &x, "symbolic-offset pointer-array byte_extract");
}
