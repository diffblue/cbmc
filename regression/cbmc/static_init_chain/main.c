#include <assert.h>

// Test case for chained static initialization dependencies
// Tests: A -> B -> C dependency chain
//
// According to C standard (C99/C11):
// - Section 6.7.9 paragraph 4: All expressions in an initializer for an
//   object that has static storage duration shall be constant expressions.
// - Section 6.6 paragraph 9: An address constant is a pointer to an lvalue
//   designating an object of static storage duration.
//
// This means c_int must be initialized before b_ptr (which points to it),
// and b_ptr must be initialized before a_ptr_ptr (which points to it).

static int c_int = 42;
static int *b_ptr = &c_int;
static int **a_ptr_ptr = &b_ptr;

int main()
{
  // Verify the entire chain is correctly initialized
  assert(a_ptr_ptr != 0);
  assert(*a_ptr_ptr != 0);
  assert(**a_ptr_ptr == 42);

  // Verify pointer values are correct
  assert(*a_ptr_ptr == b_ptr);
  assert(**a_ptr_ptr == c_int);

  return 0;
}
