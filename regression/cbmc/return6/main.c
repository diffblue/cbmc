#include <assert.h>

// Do not declare f().
// This is invalid from C99 upwards, but kind of ok before.

int main()
{
  int return_value;
  return_value=f();
  assert(return_value==0x34);
}
