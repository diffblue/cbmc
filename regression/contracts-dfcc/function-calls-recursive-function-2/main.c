#include <stdlib.h>

int sum_rec(int i, int acc)
{
  if(i >= 0)
    return sum_rec(i - 1, acc + i);
  return acc;
}

int sum(int i) __CPROVER_requires(0 <= i && i <= 50)
  __CPROVER_ensures(__CPROVER_return_value >= 0) __CPROVER_assigns()
{
  int j = i;
  int res = sum_rec(j, 0);
  return res;
}

int main()
{
  int result = sum(10);
  __CPROVER_assert(result == 55, "result == 55");
  return 0;
}
