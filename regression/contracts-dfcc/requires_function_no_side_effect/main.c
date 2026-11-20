#include <stdbool.h>

void count_pos(const int *a, int n, int *count)
{
  *count = 0;
  for(int i = 0; i < n; i++)
  {
    if(a[i] > 0)
      *count += 1;
  }
}

bool all_pos(const int *a, int n)
{
  int count;
  count_pos(a, n, &count);
  return count == n;
}

int sum(const int *a)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(a, 3 * sizeof(int)) && all_pos(a, 3))
  __CPROVER_ensures(__CPROVER_return_value > 0)
// clang-format on
{
  return a[0];
}

int main()
{
  int *a;
  sum(a);
  return 0;
}
