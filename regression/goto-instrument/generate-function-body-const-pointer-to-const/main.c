#include <assert.h>

// Edge case: both pointer and pointed-to data are const
// const int * const means neither the pointer nor the data can be modified
void havoc_const_pointer_to_const(const int *const param);

int main(void)
{
  int x = 55;
  const int *const ptr = &x;

  assert(x == 55);
  assert(*ptr == 55);

  // With both const qualifiers, havoc should not modify anything
  havoc_const_pointer_to_const(ptr);

  // Both should succeed since everything is const
  assert(x == 55);
  assert(*ptr == 55);

  return 0;
}
