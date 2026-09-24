#include <assert.h>

// Multi-level pointer const variation: int * const ** (the MIDDLE pointer is
// const). The immediate pointee of the parameter is `int * const *`, a
// non-const pointer, so the generator redirects the outer level; recursion
// then stops at the const middle pointer, leaving x and y untouched.
//
// Characterization note (#1948): this pins current, over-restrictive
// behaviour. ***triple_ptr is a non-const int and is legal C to write, so x/y
// are NOT protected by the C language -- they survive only because the havoc
// generator stops at the const middle pointer. Update the expectation if the
// generator learns to follow non-const data through const pointers.
void havoc_triple_pointer_const_middle(int *const **triple_ptr);

int main(void)
{
  int x = 42;
  int y = 100;
  int *ptr_to_x = &x;
  int *const *ptr_to_const_ptr = &ptr_to_x;
  int *const **triple_ptr = &ptr_to_const_ptr;

  assert(x == 42);             // baseline
  assert(y == 100);            // baseline
  assert(***triple_ptr == 42); // baseline

  havoc_triple_pointer_const_middle(triple_ptr);

  // The const middle pointer stops havoc traversal, so the named locals x and
  // y are preserved.
  assert(x == 42);  // SUCCESS
  assert(y == 100); // SUCCESS

  return 0;
}
