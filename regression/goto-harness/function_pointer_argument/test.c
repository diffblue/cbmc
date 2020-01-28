#include <assert.h>

typedef int (*fptr)(int a, int b);

int max_normal(int first, int second)
{
  return first >= second ? first : second;
}

int max_crazy(int first, int second)
{
  return first >= second ? second : first;
}

void use_fptr(fptr max, int first, int second)
{
  int m = max(first, second);
  assert(m == first || m == second);
  assert(m >= first && m >= second);
}
