#include <assert.h>

int main(int argc, char **argv)
{
  int total = 0;
  int n = 50;
  int i;

  for(i = 0; i < n; ++i)
  {
    total += i;
  }

  assert(total == (n * (n - 1) / 2));

  return 0;
}
