#include <assert.h>

// Edge case: volatile and const qualifiers together
// volatile const int * means pointer to volatile const data
void havoc_volatile_const_pointer(volatile const int *ptr);

int main(void)
{
  volatile int x = 77;
  volatile const int *ptr = &x;

  assert(x == 77);
  assert(*ptr == 77);

  // With const qualifier, the pointed-to value should not be modified
  // even though it's volatile
  havoc_volatile_const_pointer(ptr);

  // Should succeed due to const
  assert(x == 77);
  assert(*ptr == 77);

  return 0;
}
