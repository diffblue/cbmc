#include <assert.h>

int x;

void pure() __CPROVER_assigns()
{
  int x;
  x++;
}

int main()
{
  x = 0;
  pure();
  assert(x == 0);
  return 0;
}
