#include <assert.h>

// Edge case: nested struct with mixed const pointer qualifiers
struct inner
{
  const int *const_ptr; // pointer to const
  int *normal_ptr;      // normal pointer
};

struct outer
{
  struct inner *const const_inner_ptr;  // const pointer to struct
  struct inner *normal_inner_ptr;       // normal pointer to struct
  const struct inner *const_struct_ptr; // pointer to const struct
};

void havoc_nested_struct_const_pointers(struct outer *s);

int main(void)
{
  int x = 100, y = 200, z = 300, w = 400;

  struct inner inner1 = {&x, &y};
  struct inner inner2 = {&z, &w};
  struct outer outer_struct = {&inner1, &inner2, &inner1};

  // Initial state
  assert(x == 100);
  assert(y == 200);
  assert(z == 300);
  assert(w == 400);
  assert(*outer_struct.const_inner_ptr->const_ptr == 100);
  assert(*outer_struct.const_inner_ptr->normal_ptr == 200);

  havoc_nested_struct_const_pointers(&outer_struct);

  // Values pointed to by const pointers should be preserved
  assert(x == 100); // pointed to by const_ptr
  assert(z == 300); // pointed to by const_ptr in inner2

  // Characterization note (#1948): y and w are reachable through NON-const
  // pointers (inner.normal_ptr), so a real callee could legally write them.
  // They survive only because the havoc generator does not follow pointers
  // through nested structs -- over-restrictive behaviour that we pin here.
  // Update the expectation if the generator gains deeper struct traversal.
  assert(y == 200); // preserved - havoc doesn't reach through nested struct
  assert(w == 400); // preserved - havoc doesn't reach through nested struct

  return 0;
}
