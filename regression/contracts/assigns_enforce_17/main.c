#include <assert.h>

int x = 0;

void pure() __CPROVER_assigns()
{
  int x;
  x++;
}

int main()
{
  pure();
  assert(x == 0);
  return 0;
}
