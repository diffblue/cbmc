#include <assert.h>

// Edge case: pointer to const struct (entire struct is const)
struct test_struct
{
  int a;
  int b;
  int *ptr;
};

void havoc_pointer_to_const_struct(const struct test_struct *s);

int main(void)
{
  int x = 500;
  struct test_struct s = {10, 20, &x};

  assert(s.a == 10);
  assert(s.b == 20);
  assert(x == 500);
  assert(*s.ptr == 500);

  // Characterization note (#1948): this pins current, over-restrictive (and
  // arguably unsound) tool behaviour. `const struct test_struct *` only makes
  // the struct's own members non-assignable; *s.ptr (an int) is still legally
  // writable by a real callee. The havoc generator nevertheless skips the
  // whole parameter because its immediate pointee type is const-qualified.
  // Update the expectation if the generator learns to follow non-const
  // pointees of const structs.
  havoc_pointer_to_const_struct(&s);

  // All struct members, and the int reached via s.ptr, are preserved (this is
  // the pinned tool behaviour, not a C-language guarantee).
  assert(s.a == 10);
  assert(s.b == 20);
  assert(x == 500);
  assert(*s.ptr == 500);

  return 0;
}
