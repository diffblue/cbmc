#include <assert.h>

int y;
double z;

void bar(char **c) __CPROVER_assigns(y, z, **c) __CPROVER_ensures(**c == 6)
{
}

int main()
{
  char **b;
  bar(b);
  assert(**b == 6);

  return 0;
}
