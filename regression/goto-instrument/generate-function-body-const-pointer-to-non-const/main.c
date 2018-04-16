#include <assert.h>

void change_pointer_target_of_const_pointer(
  int *const constant_pointer_to_nonconst);

int main(void)
{
  int x = 10;
  change_pointer_target_of_const_pointer(&x);
  assert(x == 10);
  return 0;
}
