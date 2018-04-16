#include <assert.h>

void change_target_of_pointer_to_pointer_to_const(
  const int **pointer_to_pointer_to_const);

int main(void)
{
  int x = 10;
  int *px = &x;
  assert(*px == 10);
  change_target_of_pointer_to_pointer_to_const(&px);
  assert(x == 10);
  assert(*px == 10);
}
