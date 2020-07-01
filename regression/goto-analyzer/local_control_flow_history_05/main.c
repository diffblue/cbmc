#include <assert.h>

int main(int argc, char **argv)
{
  int total;
  int n;
  int i;
  int branching[4];

  total = 0;
  n = 4;
  for(i = 0; i < n; ++i)
  {
    if(branching[i])
    {
      total += i;
    }
  }

  assert(total <= (n * (n - 1) / 2));

  return 0;
}
