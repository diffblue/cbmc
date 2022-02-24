#include <stdlib.h>

void undefined_function();

void a()
{
  undefined_function();
}

void b()
{
  int should_be_sliced_away;
}

int main()
{
  int *p = malloc(sizeof(int));
  a();
  __CPROVER_assert(0, "reach me");
  b();
}
