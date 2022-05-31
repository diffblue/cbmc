#include <stdlib.h>

int main()
{
  int *a = malloc(sizeof(int) * 5);

  for(int i = 0; i < 5; i++)
    *(a + i) = i;

  for(int i = 0; i < 5; i++)
  {
    __CPROVER_assert(*(a + i) >= i, "*(a + i) >= i: expected successful");
    __CPROVER_assert(*(a + i) <= i, "*(a + i) <= i: expected successful");
    __CPROVER_assert(*(a + i) == i, "*(a + i) <= i: expected successful");
    __CPROVER_assert(*(a + i) != i, "*(a + i) <= i: expected failure");
  }
}
